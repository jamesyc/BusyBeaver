module
public import I3_380.DecoderRefinement
@[expose] public section

namespace PalomarI3380.Engine

def bit (b : Bool) : Nat := if b then 1 else 0

/-- Pack a zipper side, with the cell nearest the head first. -/
def bits : List Bool → Nat
  | [] => 0
  | b :: rest => 2 * bits rest + bit b

def atRight (q : Nat) (left right : List Bool) : Configuration :=
  ⟨q, bits left, bits right⟩

def atLeft (q : Nat) (left right : List Bool) : Configuration :=
  atRight q left.tail (left.headD false :: right)

abbrev zeros (n : Nat) : List Bool := List.replicate n false
abbrev ones (n : Nat) : List Bool := List.replicate n true

@[simp] theorem bits_mod (b : Bool) (rest : List Bool) : bits (b :: rest) % 2 = bit b := by
  cases b <;> simp only [bits, bit, Bool.false_eq_true, ↓reduceIte] <;> omega

@[simp] theorem bits_div (b : Bool) (rest : List Bool) : bits (b :: rest) / 2 = bits rest := by
  cases b <;> simp only [bits, bit, Bool.false_eq_true, ↓reduceIte] <;> omega

@[simp] theorem bits_append_zeros (t : List Bool) (n : Nat) : bits (t ++ zeros n) = bits t := by
  induction t with
  | nil =>
    simp only [List.nil_append, bits]
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ, bits, bit, Bool.false_eq_true,
        ↓reduceIte, ih, Nat.mul_zero, Nat.add_zero]
  | cons b t ih => simp only [List.cons_append, bits, ih]

@[simp] theorem atRight_pad (q : Nat) (l r : List Bool) (n : Nat) :
    atRight q l (r ++ zeros n) = atRight q l r := by
  simp only [atRight, bits_append_zeros]

@[simp] theorem atLeft_pad (q : Nat) (l r : List Bool) (n : Nat) :
    atLeft q l (r ++ zeros n) = atLeft q l r := by
  simp only [atLeft, ← List.cons_append, atRight_pad]

theorem repeat_slide (b : Bool) (n : Nat) (l : List Bool) :
    List.replicate n b ++ b :: l = b :: (List.replicate n b ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

@[simp] theorem reverse_ones (n : Nat) : (ones n).reverse = ones n := List.reverse_replicate
@[simp] theorem reverse_zeros (n : Nat) : (zeros n).reverse = zeros n := List.reverse_replicate

/-- A row assertion against the exact packed reference table. -/
def Row (q : Nat) (read write right : Bool) (target : Nat) : Prop :=
  q < referenceMachine.workingStates ∧
  referenceMachine.row q (bit read) = bit right + 2 * bit write + 4 * target

instance rowDecidable (q : Nat) (read write right : Bool) (target : Nat) :
    Decidable (Row q read write right target) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem packed_direction (d w : Bool) (q : Nat) :
    (bit d + 2 * bit w + 4 * q) % 2 = bit d := by
  cases d <;> cases w <;> simp [bit] <;> omega

private theorem packed_write (d w : Bool) (q : Nat) :
    (bit d + 2 * bit w + 4 * q) / 2 % 2 = bit w := by
  cases d <;> cases w <;> simp [bit] <;> omega

private theorem packed_target (d w : Bool) (q : Nat) :
    (bit d + 2 * bit w + 4 * q) / 4 = q := by
  cases d <;> cases w <;> simp [bit] <;> omega

theorem stepRight {q t : Nat} {b w : Bool} (h : Row q b w true t) (l r : List Bool) :
    step referenceMachine (atRight q l (b :: r)) = some (atRight t (w :: l) r) := by
  have hq : ¬referenceMachine.workingStates ≤ q := Nat.not_le.mpr h.1
  simp only [step, atRight, bits_mod, bits_div, hq, h.2, packed_direction, packed_write,
    packed_target, ↓reduceIte]
  rfl

theorem stepLeft {q t : Nat} {b w : Bool} (h : Row q b w false t) (l r : List Bool) :
    step referenceMachine (atRight q l (b :: r)) = some (atLeft t l (w :: r)) := by
  have hq : ¬referenceMachine.workingStates ≤ q := Nat.not_le.mpr h.1
  simp only [step, atLeft, atRight, bits_mod, bits_div, hq, h.2, packed_direction,
    packed_write, packed_target, ↓reduceIte]
  cases l with
  | nil =>
    simp only [List.tail_nil, List.headD_nil]
    change some (Configuration.mk t 0 (4 * bits r + 2 * bit w)) =
      some (Configuration.mk t 0 (bits (false :: w :: r)))
    simp only [bits, show bit false = 0 by rfl, Nat.add_zero, Option.some.injEq,
      Configuration.mk.injEq, true_and]
    omega
  | cons x xs =>
    simp only [List.tail_cons, List.headD_cons, bits_mod, bits_div]
    change some (Configuration.mk t (bits xs) (4 * bits r + 2 * bit w + bit x)) =
      some (Configuration.mk t (bits xs) (bits (x :: w :: r)))
    simp only [bits, Option.some.injEq, Configuration.mk.injEq, true_and]
    omega

/-- Reachability and positive reachability in the reference table. -/
def Reach (c d : Configuration) : Prop := ∃ n, run referenceMachine n c = some d
def Progress (c d : Configuration) : Prop := ∃ n, 0 < n ∧ run referenceMachine n c = some d

scoped infix:50 " ⟶* " => Reach
scoped infix:50 " ⟶+ " => Progress

theorem Reach.refl (c : Configuration) : c ⟶* c := ⟨0, rfl⟩

theorem Reach.trans {a b c : Configuration} (ab : a ⟶* b) (bc : b ⟶* c) : a ⟶* c := by
  obtain ⟨n, hn⟩ := ab
  obtain ⟨m, hm⟩ := bc
  exact ⟨n + m, join_run hn hm⟩

theorem Progress.reach {a b : Configuration} (h : a ⟶+ b) : a ⟶* b := by
  obtain ⟨n, _, runEq⟩ := h
  exact ⟨n, runEq⟩

theorem Progress.thenReach {a b c : Configuration} (ab : a ⟶+ b) (bc : b ⟶* c) : a ⟶+ c := by
  obtain ⟨n, hn, hs⟩ := ab
  obtain ⟨m, hm⟩ := bc
  exact ⟨n + m, by omega, join_run hs hm⟩

theorem Reach.thenProgress {a b c : Configuration} (ab : a ⟶* b) (bc : b ⟶+ c) : a ⟶+ c := by
  obtain ⟨n, hn⟩ := ab
  obtain ⟨m, hm, hs⟩ := bc
  exact ⟨n + m, by omega, join_run hn hs⟩

instance : Trans Reach Reach Reach := ⟨Reach.trans⟩
instance : Trans Reach Progress Progress := ⟨Reach.thenProgress⟩
instance : Trans Progress Reach Progress := ⟨Progress.thenReach⟩
instance : Trans Progress Progress Progress := ⟨fun h₁ h₂ => h₁.thenReach h₂.reach⟩

theorem right {q t : Nat} {b w : Bool} (h : Row q b w true t) (l r : List Bool) :
    atRight q l (b :: r) ⟶+ atRight t (w :: l) r := by
  exact ⟨1, by decide, by rw [run, stepRight h l r]; rfl⟩

theorem left {q t : Nat} {b w : Bool} (h : Row q b w false t) (l r : List Bool) :
    atRight q l (b :: r) ⟶+ atLeft t l (w :: r) := by
  exact ⟨1, by decide, by rw [run, stepLeft h l r]; rfl⟩

theorem scanRight {q : Nat} {b w : Bool} (h : Row q b w true q)
    (n : Nat) (l r : List Bool) :
    atRight q l (List.replicate n b ++ r) ⟶* atRight q (List.replicate n w ++ l) r := by
  induction n generalizing l with
  | zero => exact Reach.refl _
  | succ n ih =>
    change atRight q l (b :: (List.replicate n b ++ r)) ⟶*
      atRight q (w :: (List.replicate n w ++ l)) r
    rw [← repeat_slide w n l]
    exact (right h l _).reach.trans (ih (w :: l))

theorem scanLeft {q : Nat} {b w : Bool} (h : Row q b w false q)
    (n : Nat) (l r : List Bool) :
    atLeft q (List.replicate n b ++ l) r ⟶* atLeft q l (List.replicate n w ++ r) := by
  induction n generalizing r with
  | zero => exact Reach.refl _
  | succ n ih =>
    change atRight q (List.replicate n b ++ l) (b :: r) ⟶*
      atLeft q l (w :: (List.replicate n w ++ r))
    rw [← repeat_slide w n r]
    exact (left h _ r).reach.trans (ih (w :: r))

/-- Unary registers, with each positive block preceded by a separator. -/
def registers (vs : List Nat) : List Bool :=
  vs.flatMap (fun v => false :: ones (v + 1))

def reverseRegisters (vs : List Nat) : List Bool :=
  vs.flatMap (fun v => ones (v + 1) ++ [false])

@[simp] theorem registers_cons (v : Nat) (vs : List Nat) :
    registers (v :: vs) = false :: true :: (ones v ++ registers vs) := rfl

@[simp] theorem reverseRegisters_cons (v : Nat) (vs : List Nat) :
    reverseRegisters (v :: vs) = true :: (ones v ++ false :: reverseRegisters vs) := by
  simp only [reverseRegisters, List.flatMap_cons, List.replicate_succ, List.cons_append,
    List.append_assoc, List.nil_append]

@[simp] theorem registers_append (vs ws : List Nat) :
    registers (vs ++ ws) = registers vs ++ registers ws := List.flatMap_append

@[simp] theorem reverseRegisters_append (vs ws : List Nat) :
    reverseRegisters (vs ++ ws) = reverseRegisters vs ++ reverseRegisters ws := List.flatMap_append

theorem registers_reverse (vs : List Nat) : (registers vs).reverse = reverseRegisters vs.reverse := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [registers_cons, List.reverse_cons, List.reverse_append, reverse_ones, ih,
      reverseRegisters, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.replicate_succ]
    simp only [List.append_assoc, repeat_slide, List.append_nil]

theorem reverseRegisters_reverse (vs : List Nat) :
    (reverseRegisters vs).reverse = registers vs.reverse := by
  have h := registers_reverse vs.reverse
  rw [List.reverse_reverse] at h
  rw [← h, List.reverse_reverse]

end PalomarI3380.Engine
