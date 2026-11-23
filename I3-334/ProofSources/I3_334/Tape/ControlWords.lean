module
public import I3_334.Tape.StockScans
public import I3_334.Literal
public import I3_334.Machine.ReferenceData
public import I3_334Support.Engine.Arithmetic.WindowReplay
@[expose] public section

namespace PalomarI3334.Control

open PalomarI3380
open PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell repeatZero_slide)
open PalomarI3380.Engine (leadingZeros breakPath breakPadding incrementReversed stripThrough)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- Five zeros may occur in a reversed instruction pointer. Six mark
the end of the pointer during the leftward return. -/
def boundedZeros (seen : Nat) : List Bool → Bool
  | [] => true
  | true :: rest => boundedZeros 0 rest
  | false :: rest => decide (seen < 5) && boundedZeros (seen + 1) rest

theorem boundedZeros_mono {a b : Nat} {path : List Bool} (h : a ≤ b)
    (valid : boundedZeros b path = true) : boundedZeros a path = true := by
  induction path generalizing a b with
  | nil => rfl
  | cons bit path ih =>
    cases bit
    · simp only [boundedZeros, Bool.and_eq_true, decide_eq_true_eq] at valid ⊢
      exact ⟨by omega, ih (by omega) valid.2⟩
    · exact valid

theorem boundedZeros_tail {b : Bool} {path : List Bool}
    (valid : boundedZeros 0 (b :: path) = true) : boundedZeros 0 path = true := by
  cases b
  · simp only [boundedZeros, Bool.and_eq_true] at valid
    exact boundedZeros_mono (by decide : 0 ≤ 1) valid.2
  · exact valid

theorem boundedZeros_ones (n : Nat) (path : List Bool) :
    boundedZeros 0 (List.replicate n true ++ path) = boundedZeros 0 path := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem boundedZeros_of_leading (path : List Bool) (seen : Nat)
    (valid : boundedZeros 0 path = true)
    (bound : seen + leadingZeros path ≤ 5) : boundedZeros seen path = true := by
  induction path generalizing seen with
  | nil => rfl
  | cons bit path ih =>
    cases bit
    · have rest := boundedZeros_tail valid
      simp only [leadingZeros] at bound
      simp only [boundedZeros, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, ih (seen + 1) rest (by omega)⟩
    · exact valid

abbrev root : Nat := 16
abbrev dispatch (seen : Nat) : Nat := 9 + seen
abbrev continuePort (skip : Nat) : Nat := 9 - skip
abbrev breakPort (skip : Bool) : Nat := if skip then 24 else 33

/-- All four tables have the same instruction-pointer return ports.
The short checked trace crosses a blank left flank and the marker,
leaving the arithmetic-model tape to its right untouched. -/
structure Rows (m : Machine) : Prop where
  one : ∀ seen : Fin 6, Stock.Row m (dispatch seen.val) true true false (dispatch 0)
  zero : ∀ seen : Fin 5, Stock.Row m (dispatch seen.val) false false false (dispatch (seen.val + 1))
  breakZero : Stock.Row m 33 false true false (dispatch 0)
  skipZero : Stock.Row m 24 false false false 33
  carry : ∀ skip : Bool, Stock.Row m (breakPort skip) true false false (breakPort skip)
  continueZero : ∀ skip : Fin 4,
    Stock.Row m (continuePort (skip.val + 1)) false false false (continuePort (skip.val + 1))
  continueOne : ∀ skip : Fin 4,
    Stock.Row m (continuePort (skip.val + 1)) true false false (continuePort skip.val)
  blankDispatch : DecoderWindow.runToMatch m ⟨⟨root, 1, 0⟩, 11, 0⟩ 12
    ⟨⟨dispatch 0, 0, 2⟩, 9, 2⟩ = some 12
  blankBreak : ∀ skip : Bool,
    DecoderWindow.runToMatch m ⟨⟨root, 1, 0⟩, (if skip then 8 else 9), (if skip then 2 else 1)⟩
      (if skip then 15 else 14) ⟨⟨breakPort skip, 0, 1⟩, 9, 1⟩ =
        some (if skip then 15 else 14)

theorem literalRows : Rows machine := by
  constructor <;> decide +kernel

theorem referenceRows : Rows decoderReference := by
  constructor <;> decide +kernel

variable {m : Machine}
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem marker : (1 : M) = pushBit true 0 := by simp [pushBit]

private theorem dispatchBlank (rows : Rows m) (y : M) :
    Reaches m (fromLeft (dispatch 0) 0 (pushBit true y)) (cell root 1 y) := by
  refine ⟨12, ?_⟩
  have h := window_run rows.blankDispatch (0 : M) y
  have four : ((2^2 : Nat) : M) = 4 := by norm_num
  have two : (2 : M) * 2 = 4 := by exact_mod_cast (show (2 : Nat) * 2 = 4 from rfl)
  simp only [windowCode, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero,
    Nat.pow_zero, one_mul, zero_add, fromLeft, cell, pushBit, Bool.toNat_true,
    divIn, remIn, Arithmetic.zero_div, Arithmetic.zero_mod] at h ⊢
  simpa only [mul_add, mul_one, ← mul_assoc, two, four, add_comm (2 : M), zero_add, add_zero,
    Nat.cast_ofNat] using h

/-- Return over a bounded reversed instruction pointer without inspecting
the model-valued suffix. -/
theorem dispatchFrom (rows : Rows m) (path : List Bool) (seen : Nat)
    (limit : seen ≤ 5) (valid : boundedZeros seen path = true) (y : M) :
    Reaches m (fromLeft (dispatch seen) (packWord path 1) y)
      (cell root 1 (packWord path.reverse y)) := by
  induction path generalizing seen y with
  | nil =>
    change Reaches m (fromLeft (dispatch seen) 1 y) (cell root 1 y)
    have start : fromLeft (dispatch seen) 1 y = cell (dispatch seen) 0 (pushBit true y) := by
      rw [marker, fromLeft_pushBit]
      rfl
    rw [start]
    exact (Stock.left (rows.one ⟨seen, by omega⟩) 0 y).trans (dispatchBlank rows y)
  | cons bit path ih =>
    change Reaches m (fromLeft (dispatch seen) (pushBit bit (packWord path 1)) y)
      (cell root 1 (packWord (bit :: path).reverse y))
    rw [fromLeft_pushBit, List.reverse_cons, packWord_append]
    cases bit
    · obtain ⟨below, rest⟩ : seen < 5 ∧ boundedZeros (seen+1) path = true := by
        simpa [boundedZeros] using valid
      exact (Stock.left (rows.zero ⟨seen, below⟩) (packWord path 1) y).trans
        (ih (seen+1) (by omega) rest (pushBit false y))
    · exact (Stock.left (rows.one ⟨seen, by omega⟩) (packWord path 1) y).trans
        (ih 0 (by decide) valid (pushBit true y))

private theorem breakBlank (rows : Rows m) (skip : Bool) (y : M) :
    Reaches m (fromLeft (breakPort skip) 1 y)
      (cell root 1 (repeatBit false ((breakPadding skip [] : Nat) : M) y)) := by
  cases skip with
  | false =>
    refine ⟨14, ?_⟩
    have h := window_run (rows.blankBreak false) (0 : M) y
    rw [marker, fromLeft_pushBit, ← marker]
    simpa [windowCode, cell, pushBit, breakPadding, repeatBit_one, add_comm] using h
  | true =>
    refine ⟨15, ?_⟩
    have h := window_run (rows.blankBreak true) (0 : M) y
    rw [marker, fromLeft_pushBit, ← marker]
    have two : (2 : M) * 2 = 4 := by exact_mod_cast (show (2 : Nat) * 2 = 4 from rfl)
    have after : repeatBit false 2 y = (4 : M)*y := by
      rw [← one_add_one_eq_two, repeatBit_succ, repeatBit_one]
      simp [pushBit, ← mul_assoc, two]
    simpa [windowCode, cell, pushBit, breakPadding, after, add_comm] using h

theorem breakRun (rows : Rows m) (skip : Bool) (path : List Bool)
    (valid : boundedZeros 0 path = true) (y : M) :
    Reaches m (fromLeft (breakPort skip) (packWord path 1) y)
      (cell root 1 (packWord (breakPath skip path).reverse
        (repeatBit false ((breakPadding skip path : Nat) : M) y))) := by
  induction path generalizing skip y with
  | nil =>
    cases skip
    · simpa [breakPath, incrementReversed, stripThrough] using breakBlank rows false y
    · simpa [breakPath, incrementReversed, stripThrough] using breakBlank rows true y
  | cons bit path ih =>
    have rest := boundedZeros_tail valid
    change Reaches m (fromLeft (breakPort skip) (pushBit bit (packWord path 1)) y) _
    rw [fromLeft_pushBit]
    change Reaches m (cell (breakPort skip) (packWord path 1) (pushBit bit y)) _
    cases bit <;> cases skip
    · have move := Stock.left rows.breakZero (packWord path 1) y
      simpa only [breakPort, breakPath, Bool.false_eq_true, ↓reduceIte, incrementReversed, breakPadding,
        Nat.cast_zero, repeatBit_zero, List.reverse_cons, packWord_append, packWord_cons,
        packWord_nil] using move.trans (dispatchFrom rows path 0 (by decide) rest (pushBit true y))
    · have move := Stock.left rows.skipZero (packWord path 1) y
      simpa only [breakPort, breakPath, Bool.false_eq_true, ↓reduceIte, stripThrough, breakPadding,
        Nat.cast_succ, repeatZero_slide] using move.trans (ih false rest (pushBit false y))
    · have move := Stock.left (rows.carry false) (packWord path 1) y
      simpa only [breakPort, breakPath, Bool.false_eq_true, ↓reduceIte, incrementReversed, breakPadding,
        Nat.add_zero, List.reverse_cons, packWord_append, packWord_cons, packWord_nil,
        repeatBit_push] using move.trans (ih false rest (pushBit false y))
    · have move := Stock.left (rows.carry true) (packWord path 1) y
      simpa only [breakPort, breakPath, ↓reduceIte, stripThrough, Bool.true_eq_false, breakPadding,
        Nat.cast_succ, repeatZero_slide] using move.trans (ih true rest (pushBit false y))

/-- Remove the requested number of one bits and all intervening zeros. -/
def cut : List Bool → Nat → List Bool
  | [], _ => []
  | bit :: rest, 0 => bit :: rest
  | false :: rest, n + 1 => cut rest (n + 1)
  | true :: rest, n + 1 => cut rest n

def ones : List Bool → Nat
  | [] => 0
  | b :: rest => b.toNat + ones rest

theorem cut_length (path : List Bool) (skip : Nat) : (cut path skip).length ≤ path.length := by
  induction path generalizing skip with
  | nil => exact Nat.le_refl _
  | cons bit path ih =>
    cases skip with
    | zero => cases bit <;> exact Nat.le_refl _
    | succ n =>
      cases bit
      · exact Nat.le_trans (ih (n+1)) (Nat.le_succ _)
      · exact Nat.le_trans (ih n) (Nat.le_succ _)

theorem continueRun (rows : Rows m) (path : List Bool) (skip : Nat) (limit : skip ≤ 4)
    (valid : boundedZeros 0 path = true) (enough : skip ≤ ones path) (y : M) :
    Reaches m (fromLeft (continuePort skip) (packWord path 1) y)
      (cell root 1 (packWord (cut path skip).reverse
        (repeatBit false ((path.length - (cut path skip).length : Nat) : M) y))) := by
  induction path generalizing skip y with
  | nil =>
    have eq : skip = 0 := by simpa [ones] using enough
    subst skip
    simpa [cut] using dispatchFrom rows [] 0 (by decide) rfl y
  | cons bit path ih =>
    cases skip with
    | zero =>
      simpa [cut] using dispatchFrom rows (bit :: path) 0 (by decide) valid y
    | succ skip =>
      let n : Fin 4 := ⟨skip, by omega⟩
      have rest := boundedZeros_tail valid
      change Reaches m (fromLeft (continuePort (skip+1)) (pushBit bit (packWord path 1)) y) _
      rw [fromLeft_pushBit]
      change Reaches m (cell (continuePort (skip+1)) (packWord path 1) (pushBit bit y)) _
      cases bit
      · have enough' : skip + 1 ≤ ones path := by simpa [ones] using enough
        have pad : path.length + 1 - (cut path (skip+1)).length =
            path.length - (cut path (skip+1)).length + 1 := by
          have := cut_length path (skip+1)
          omega
        have move := Stock.left (rows.continueZero n) (packWord path 1) y
        simpa only [n, cut, List.length_cons, pad, Nat.cast_succ, repeatZero_slide] using
          move.trans (ih (skip+1) limit rest enough' (pushBit false y))
      · have enough' : skip ≤ ones path := by simp [ones] at enough; omega
        have pad : path.length + 1 - (cut path skip).length =
            path.length - (cut path skip).length + 1 := by
          have := cut_length path skip
          omega
        have move := Stock.left (rows.continueOne n) (packWord path 1) y
        simpa only [n, cut, List.length_cons, pad, Nat.cast_succ, repeatZero_slide] using
          move.trans (ih skip (by omega) rest enough' (pushBit false y))

end PalomarI3334.Control
