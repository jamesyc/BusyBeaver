module
public import I0451.Tables
public import I0451.TapeRuns

/-! Direct proof for the literal decoder. A contraction reads the current
bit and may temporarily look at either of the two bits to its left.
Each result is a single logical descent or a register/return instruction.
The tapes outside those three cells stay arbitrary throughout. -/

@[expose] public section
namespace I0451.Decoder

def rank (q : Nat) (a b : Bool) : Nat :=
  if q < 451 then digit decoderRanks (4 * q + a.toNat + 2 * b.toNat) else 0

def issuing (q : Nat) : Bool :=
  q == 451 || incStates.contains q || decStates.contains q

def returning (q : Nat) : Bool :=
  q == breakOne || q == continueZero || q == continueOne

def atRuntime (q : Nat) : Bool := issuing q || returning q

/-- The kind of leaf reached after the logical decoder consumes a word. -/
inductive Exit where
  | issue (state : Nat)
  | erase (state : Nat)
  | fused
  deriving DecidableEq, Repr

/-- Semantic outcomes of a logical decoder arm, in terms of the original
three cells. An internal arm moves right, preserving the input bit.
Return instructions erase one or two cells and move that far left. -/
inductive Outcome (q : Nat) (a b read : Bool) : Window → Sum Nat Exit → Prop where
  | descend (t : Nat) (positive : 0 < rank t read a) (decreases : rank t read a < rank q a b) :
      Outcome q a b read ⟨t, [read, a, b], []⟩ (.inl t)
  | issue (t : Nat) (valid : issuing t = true) :
      Outcome q a b read ⟨t, [read, a, b], []⟩ (.inr (.issue t))
  | one (t : Nat) (valid : returning t = true) (ready : read = true) :
      Outcome q a b read ⟨t, [b], [a, false]⟩ (.inr (.erase t))
  | two (ready : read = true) (previous : a = true) :
      Outcome q a b read ⟨continueOne, [], [b, false, false]⟩ (.inr .fused)

/-- Recognize the exact tape effect and next logical control of an arm. -/
def classify (q : Nat) (a b read : Bool) (out : Window) : Option (Sum Nat Exit) :=
  if out.left == [read, a, b] && out.right == [] then
    if 0 < rank out.state read a ∧ rank out.state read a < rank q a b then
      some (.inl out.state)
    else if issuing out.state then
      some (.inr (.issue out.state))
    else none
  else if out.left == [b] && out.right == [a, false] && returning out.state && read then
    some (.inr (.erase out.state))
  else if out.left == [] && out.right == [b, false, false] && out.state == continueOne && read && a then
    some (.inr .fused)
  else none

theorem classify_sound {q : Nat} {a b read : Bool} {out : Window} {target : Sum Nat Exit}
    (h : classify q a b read out = some target) : Outcome q a b read out target := by
  obtain ⟨t, l, r⟩ := out
  unfold classify at h
  split at h
  · rename_i shape
    simp only [Bool.and_eq_true, beq_iff_eq] at shape
    obtain ⟨rfl, rfl⟩ := shape
    split at h
    · rename_i ranks
      injection h with eq
      subst target
      exact .descend t ranks.1 ranks.2
    · split at h
      · rename_i valid
        injection h with eq
        subst target
        exact .issue t valid
      · contradiction
  · split at h
    · rename_i shape
      simp only [Bool.and_eq_true, beq_iff_eq] at shape
      obtain ⟨⟨⟨rfl, rfl⟩, valid⟩, ready⟩ := shape
      injection h with eq
      subst target
      exact .one t valid ready
    · split at h
      · rename_i shape
        simp only [Bool.and_eq_true, beq_iff_eq] at shape
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, ready⟩, previous⟩ := shape
        injection h with eq
        subst target
        exact .two ready previous
      · contradiction

/-- Simulate a bounded number of literal moves within the known window. -/
def candidate (q : Nat) (a b read : Bool) (n : Nat) : Option (Sum Nat Exit) :=
  ((Window.seed q a b read).run literal (n + 1)).bind (classify q a b read)

/-- Find an accepted contraction of at most three physical steps. -/
def arm (q : Nat) (a b read : Bool) : Option (Sum Nat Exit) :=
  (List.range 3).findSome? (candidate q a b read)

theorem arm_sound {q : Nat} {a b read : Bool} {target : Sum Nat Exit}
    (found : arm q a b read = some target) :
    ∃ (n : Nat) (out : Window), n < 3 ∧ (Window.seed q a b read).run literal (n + 1) = some out ∧
      Outcome q a b read out target := by
  obtain ⟨n, member, verified⟩ := List.exists_of_findSome?_eq_some found
  cases h : (Window.seed q a b read).run literal (n + 1) with
  | none => simp [candidate, h] at verified
  | some out =>
    exact ⟨n, out, List.mem_range.mp member, h,
      classify_sound (by simpa [candidate, h] using verified)⟩

private def bits : List Bool := [false, true]

private theorem mem_bits (b : Bool) : b ∈ bits := by cases b <;> decide

private def checkContext (q : Nat) (a b : Bool) : Bool :=
  rank q a b == 0 || bits.all (fun read => (arm q a b read).isSome)

private def checkRanks (states : List Nat) : Bool :=
  states.all (fun q => bits.all (fun a => bits.all (checkContext q a)))

-- Each half is checked separately to bound reduction in independent kernels.
private theorem checkedLow : checkRanks (List.range 226) = true := by decide +kernel
private theorem checkedHigh : checkRanks (List.range' 226 225) = true := by decide +kernel

private theorem checked (q : Nat) (bound : q < 451) :
    bits.all (fun a => bits.all (checkContext q a)) = true := by
  by_cases low : q < 226
  · exact List.all_eq_true.mp checkedLow q (List.mem_range.mpr low)
  · apply List.all_eq_true.mp checkedHigh q
    have inRange : 226 ≤ q ∧ q < 226 + 225 := by omega
    simpa only [List.mem_range'_1] using inRange

/-- Every live logical arm has a checked contraction. -/
theorem arm_complete {q : Nat} {a b read : Bool} (live : 0 < rank q a b) :
    (arm q a b read).isSome = true := by
  have bound : q < 451 := by
    by_cases h : q < 451
    · exact h
    · simp [rank, h] at live
  have checkA := List.all_eq_true.mp (checked q bound) a (mem_bits a)
  have checkB := List.all_eq_true.mp checkA b (mem_bits b)
  have nonzero : (rank q a b == 0) = false := by
    cases bitEq : rank q a b == 0
    · rfl
    · have zero := beq_iff_eq.mp bitEq
      omega
  simp only [checkContext, nonzero, Bool.false_or] at checkB
  exact List.all_eq_true.mp checkB read (mem_bits read)

/-- The tape at the end of a decoder word, including any erased cells.
The supplied left stack starts with the last cell of that word. -/
def Exit.place (exit : Exit) (left right : Nat) : Config :=
  match exit with
  | .issue q => ⟨q, left, right⟩
  | .erase q => fromLeft q (left / 2) (push false right)
  | .fused => fromLeft continueOne (left / 2 / 2) (push false (push false right))

/-- A path of contractions of the literal table. Every constructor except
`next` performs the last read and implements a specific leaf effect. -/
inductive Path : Nat → Bool → Bool → List Bool → Exit → Prop
  | issue (q : Nat) (a b read : Bool) (t n : Nat) (short : n < 3)
      (moves : (Window.seed q a b read).run literal (n + 1) =
        some ⟨t, [read, a, b], []⟩) (valid : issuing t = true) :
      Path q a b [read] (.issue t)
  | erase (q : Nat) (a b : Bool) (t n : Nat) (short : n < 3)
      (moves : (Window.seed q a b true).run literal (n + 1) =
        some ⟨t, [b], [a, false]⟩) (valid : returning t = true) :
      Path q a b [true] (.erase t)
  | fused (q : Nat) (b : Bool) (n : Nat) (short : n < 3)
      (moves : (Window.seed q true b true).run literal (n + 1) =
        some ⟨continueOne, [], [b, false, false]⟩) :
      Path q true b [true] .fused
  | next (q : Nat) (a b read : Bool) (t n : Nat) {rest : List Bool} {exit : Exit}
      (short : n < 3)
      (moves : (Window.seed q a b read).run literal (n + 1) =
        some ⟨t, [read, a, b], []⟩) (more : Path t read a rest exit) :
      Path q a b (read :: rest) exit

/-- An issuing path leaves the whole consumed word unchanged. -/
abbrev IssuePath (q : Nat) (a b : Bool) (word : List Bool) (t : Nat) :=
  Path q a b word (.issue t)

theorem Path.read {q : Nat} {exit : Exit} {a b : Bool} {word : List Bool}
    (path : Path q a b word exit) (l r : Nat) :
    ∃ n, 0 < n ∧ n ≤ 3 * word.length ∧
      run literal n ⟨q, push a (push b l), pack word r⟩ =
        some (exit.place (pack word.reverse (push a (push b l))) r) := by
  induction path generalizing l r with
  | issue q a b read t ticks short moves valid =>
    exact ⟨ticks + 1, by omega, by simp; omega, Window.run_extend moves l r⟩
  | erase q a b t ticks short moves valid =>
    refine ⟨ticks + 1, by omega, by simp; omega, ?_⟩
    simpa [Exit.place, Window.extend, Window.seed] using Window.run_extend moves l r
  | fused q b ticks short moves =>
    refine ⟨ticks + 1, by omega, by simp; omega, ?_⟩
    simpa [Exit.place, Window.extend, Window.seed] using Window.run_extend moves l r
  | @next q a b read t ticks rest exit short moves path ih =>
    obtain ⟨m, pos, bound, later⟩ := ih (push b l) r
    have first : run literal (ticks + 1)
        ⟨q, push a (push b l), push read (pack rest r)⟩ =
        some ⟨t, push read (push a (push b l)), pack rest r⟩ :=
      Window.run_extend moves l (pack rest r)
    refine ⟨ticks + 1 + m, by omega, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · simp only [pack_cons, List.reverse_cons, pack_append, pack_nil]
      exact run_join first later rfl

theorem IssuePath.read_root {t : Nat} {word : List Bool}
    (path : IssuePath root true false word t) (r : Nat) :
    Reaches literal ⟨root, 1, pack word r⟩ ⟨t, pack word.reverse 1, r⟩ := by
  have marker : push true (push false 0) = 1 := rfl
  obtain ⟨n, _, _, result⟩ := Path.read path 0 r
  exact ⟨n, by simpa only [marker, Exit.place] using result⟩

theorem Path.runtime {q : Nat} {exit : Exit} {a b : Bool} {word : List Bool}
    (path : Path q a b word exit) (l r : Nat) :
    atRuntime (exit.place l r).state = true := by
  induction path with
  | issue q a b read t ticks short moves valid => simp [atRuntime, Exit.place, valid]
  | erase q a b t ticks short moves valid => simp [atRuntime, Exit.place, fromLeft, valid]
  | fused q b ticks short moves => simp [atRuntime, Exit.place, fromLeft, returning]
  | next _ _ _ _ _ _ _ _ _ ih => exact ih

structure Decoded where
  word : List Bool
  rest : Nat
  exit : Exit
  deriving DecidableEq, Repr

/-- Executable logical decoding, using the same checked local contractions
as the physical path proof. -/
def decode : Nat → Nat → Bool → Bool → Nat → Option Decoded
  | 0, _, _, _, _ => none
  | fuel + 1, q, a, b, right =>
    match arm q a b (bit right) with
    | none => none
    | some (.inr exit) => some ⟨[bit right], right / 2, exit⟩
    | some (.inl target) =>
      (decode fuel target (bit right) a (right / 2)).map
        (fun tail => { tail with word := bit right :: tail.word })

theorem decode_sound {fuel q right : Nat} {a b : Bool} {result : Decoded}
    (h : decode fuel q a b right = some result) :
    right = pack result.word result.rest ∧ result.word.length ≤ fuel ∧
      Path q a b result.word result.exit := by
  induction fuel generalizing q a b right result with
  | zero => simp [decode] at h
  | succ fuel ih =>
    cases found : arm q a b (bit right) with
    | none => simp [decode, found] at h
    | some target =>
      obtain ⟨n, out, short, moves, outcome⟩ := arm_sound found
      cases outcome with
      | descend t positive decreases =>
        cases next : decode fuel t (bit right) a (right / 2) with
        | none => simp [decode, found, next] at h
        | some tail =>
          have tailSound := ih next
          simp only [decode, found, next, Option.map_some, Option.some.injEq] at h
          subst result
          refine ⟨?_, ?_, .next q a b (bit right) t n short moves tailSound.2.2⟩
          · rw [pack_cons, ← tailSound.1, push_bit_pop]
          · simp only [List.length_cons]
            omega
      | issue t valid =>
        simp only [decode, found, Option.some.injEq] at h
        subst result
        exact ⟨(push_bit_pop right).symm, by simp, .issue q a b (bit right) t n short moves valid⟩
      | one t valid isOne =>
        simp only [decode, found, Option.some.injEq] at h
        subst result
        have tape := (push_bit_pop right).symm
        rw [isOne] at tape moves ⊢
        exact ⟨tape, by simp, .erase q a b t n short moves valid⟩
      | two isOne previous =>
        subst a
        simp only [decode, found, Option.some.injEq] at h
        subst result
        have tape := (push_bit_pop right).symm
        rw [isOne] at tape moves ⊢
        exact ⟨tape, by simp, .fused q b n short moves⟩

theorem decode_total {fuel q right : Nat} {a b : Bool} (live : 0 < rank q a b)
    (bound : rank q a b ≤ fuel) : (decode fuel q a b right).isSome = true := by
  induction fuel generalizing q a b right with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨target, found⟩ := Option.isSome_iff_exists.mp (arm_complete (read := bit right) live)
    obtain ⟨n, out, short, moves, outcome⟩ := arm_sound found
    cases outcome with
    | descend t positive decreases =>
      have tail := ih (right := right / 2) positive (by omega)
      simp [decode, found, tail]
    | issue t valid => simp [decode, found]
    | one t valid ready => simp [decode, found]
    | two ready previous => simp [decode, found]

/-- The decoder consumes a bounded path. Its word is an actual prefix
of the input tape and the rest remains available to the runtime. -/
theorem exists_path {q : Nat} {a b : Bool} (live : 0 < rank q a b) (right : Nat) :
    ∃ word suffix exit, right = pack word suffix ∧ word.length ≤ rank q a b ∧
      Path q a b word exit := by
  obtain ⟨result, parsed⟩ := Option.isSome_iff_exists.mp
    (decode_total (right := right) live (Nat.le_refl _))
  exact ⟨result.word, result.rest, result.exit, decode_sound parsed⟩

theorem root_rank (a b : Bool) : rank root a b = 94 := by
  cases a <;> cases b <;> decide +kernel

/-- At the literal decoder root, a runtime control is reached within 282
physical steps for every tape. -/
theorem root_reaches_runtime (left right : Nat) :
    ∃ (n : Nat) (finish : Config), 0 < n ∧ n ≤ 282 ∧
      run literal n ⟨root, left, right⟩ = some finish ∧ atRuntime finish.state = true := by
  let a := bit left
  let b := bit (left / 2)
  have live : 0 < rank root a b := by rw [root_rank]; decide
  obtain ⟨word, suffix, exit, split, length, path⟩ := exists_path live right
  obtain ⟨n, pos, bound, moves⟩ := path.read (left / 2 / 2) suffix
  rw [root_rank] at length
  simp only [a, b, push_bit_pop, ← split] at moves
  exact ⟨n, _, pos, by omega, moves, path.runtime _ _⟩

end I0451.Decoder
