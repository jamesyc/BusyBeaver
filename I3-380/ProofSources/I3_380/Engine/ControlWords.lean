module
public import I3_380.Engine.RegisterPorts
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine

namespace Port

abbrev continueOne := 46

def dispatch (n : Nat) : Nat := #[39, 59, 78, 94, 105, 110, 116][n]?.getD 394

end Port

/-- The dispatcher recognises the left marker after crossing seven zeros.
Inside the instruction pointer it can cross at most six in a row. -/
def shortZeros (seen : Nat) : List Bool → Bool
  | [] => true
  | true :: rest => shortZeros 0 rest
  | false :: rest => decide (seen < 6) && shortZeros (seen + 1) rest

theorem shortZeros_mono {a b : Nat} {path : List Bool} (hle : a ≤ b)
    (h : shortZeros b path = true) : shortZeros a path = true := by
  induction path generalizing a b with
  | nil => rfl
  | cons bit rest ih =>
    cases bit
    · simp only [shortZeros, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨by omega, ih (by omega) h.2⟩
    · exact h

theorem shortZeros_tail {b : Bool} {path : List Bool} (h : shortZeros 0 (b :: path) = true) :
    shortZeros 0 path = true := by
  cases b
  · simp only [shortZeros, Bool.and_eq_true] at h
    exact shortZeros_mono (by omega) h.2
  · exact h

theorem shortZeros_ones (n : Nat) (path : List Bool) :
    shortZeros 0 (ones n ++ path) = shortZeros 0 path := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem dispatch_one : ∀ seen : Fin 7,
    Row (Port.dispatch seen.val) true true false (Port.dispatch 0) := by
  decide +kernel

theorem dispatch_zero : ∀ seen : Fin 6,
    Row (Port.dispatch seen.val) false false false (Port.dispatch (seen.val + 1)) := by
  decide +kernel

def incrementReversed : List Bool → List Bool
  | [] => []
  | false :: path => true :: path
  | true :: path => false :: incrementReversed path

@[simp] theorem incrementReversed_length (path : List Bool) :
    (incrementReversed path).length = path.length := by
  induction path with
  | nil => rfl
  | cons b path ih => cases b <;> simp only [incrementReversed, List.length_cons, ih]

def stripThrough (bit : Bool) : List Bool → List Bool
  | [] => []
  | b :: path => if b = bit then path else stripThrough bit path

theorem stripThrough_length (bit : Bool) (path : List Bool) :
    (stripThrough bit path).length ≤ path.length := by
  induction path with
  | nil => exact Nat.le_refl 0
  | cons b path ih =>
    simp only [stripThrough, List.length_cons]
    split <;> omega

def breakPath (skipZero : Bool) (path : List Bool) : List Bool :=
  incrementReversed (if skipZero then stripThrough false path else path)

def breakPadding (skipZero : Bool) : List Bool → Nat
  | [] => if skipZero then 2 else 1
  | false :: rest => if skipZero then breakPadding false rest + 1 else 0
  | true :: rest => breakPadding skipZero rest + if skipZero then 1 else 0

theorem break_length (skipZero : Bool) (path : List Bool) :
    path.length ≤ (breakPath skipZero path).length + breakPadding skipZero path := by
  induction path generalizing skipZero with
  | nil => simp
  | cons b path ih =>
    cases b <;> cases skipZero <;>
      simp only [breakPath, incrementReversed, incrementReversed_length, breakPadding, stripThrough,
        Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, List.length_cons, Nat.add_zero]
    · omega
    · omega
    · have h := ih false
      simp only [breakPath, Bool.false_eq_true, ↓reduceIte, incrementReversed_length] at h
      omega
    · have h := ih true
      simp only [breakPath, ↓reduceIte, incrementReversed_length] at h
      omega

theorem break_carry (skipZero : Bool) :
    Row (Port.breakPort skipZero) true false false (Port.breakPort skipZero) := by
  cases skipZero <;> decide +kernel

theorem increment_after_marks (n : Nat) (reversed : List Bool) :
    incrementReversed (ones n ++ reversed) = zeros n ++ incrementReversed reversed := by
  induction n with
  | zero => rfl
  | succ _ ih => simp only [List.replicate_succ, List.cons_append, incrementReversed, ih]

theorem strip_after_marks (n : Nat) (reversed : List Bool) :
    stripThrough false (ones n ++ reversed) = stripThrough false reversed := by
  induction n with
  | zero => rfl
  | succ _ ih =>
    simpa only [List.replicate_succ, List.cons_append, stripThrough, Bool.true_eq_false,
      ↓reduceIte] using ih

theorem break_padding_after_marks (skip : Bool) (n : Nat) (reversed : List Bool) :
    breakPadding skip (ones n ++ reversed) =
      breakPadding skip reversed + if skip then n else 0 := by
  induction n with
  | zero => cases skip <;> exact (Nat.add_zero _).symm
  | succ n ih =>
    change breakPadding skip (true :: (ones n ++ reversed)) = _
    rw [breakPadding, ih]
    cases skip <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.add_assoc]

def registerValue {V : Type} [OfNat V 0] [OfNat V 1] [Sub V] [Add V] [DecidableEq V]
    (dec : Bool) (value : V) : V :=
  if dec then (if value = 0 then 0 else value - 1) else value + 1

def zeroDecrement {V : Type} [OfNat V 0] [DecidableEq V] (dec : Bool) (value : V) : Bool :=
  dec && decide (value = 0)

end PalomarI3380.Engine
