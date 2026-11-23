module
public import I3_334Support.Engine.Tape
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine

/-- Number of consecutive zeros next to the head, in a reversed path. -/
def leadingZeros : List Bool → Nat
  | [] => 0
  | true :: _ => 0
  | false :: rest => leadingZeros rest + 1

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
