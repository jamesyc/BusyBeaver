module
public import I3_334Support.Machine
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
