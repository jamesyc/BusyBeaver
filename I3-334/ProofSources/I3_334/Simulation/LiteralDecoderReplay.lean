module
public import I3_334.Simulation.LiteralDecoderRows
public import I3_334.Tape.Progress
@[expose] public section

namespace PalomarI3334.LiteralDecoder

open PalomarI3380 PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell)
open PalomarI3380.DecoderWindow
open Decoder (transition)
open Stock (Progress)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A finite window certificate is interpreted in the model, with no
bound on either of the tape tails. -/
theorem verifies_run {src dst : DecoderWindow} {fuel : Nat} (checked : verifies src dst fuel = true)
    (l r : M) : Progress machine (windowCode (translateWindow src) l r)
      (windowCode (translateWindow dst) l r) := by
  cases trace : runToMatch machine (translateWindow dst) fuel (translateWindow src) with
  | none => simp [verifies, trace] at checked
  | some n =>
    have positive : 0 < n := by simpa only [verifies, trace, decide_eq_true_eq] using checked
    exact ⟨(n : M), by exact_mod_cast positive, window_run trace l r⟩

noncomputable def reindex (q : Nat) (code : M) : M :=
  cell q (π₁ (π₂ code)) (π₂ (π₂ code))

@[simp] theorem reindex_cell (q q' : Nat) (left right : M) :
    reindex q (cell q' left right) = cell q left right := by
  simp only [reindex, cell, encode, Arithmetic.pi₁_pair, Arithmetic.pi₂_pair]

@[simp] theorem reindex_fromLeft (q q' : Nat) (left right : M) :
    reindex q (fromLeft q' left right) = fromLeft q left right := by
  simp only [reindex, cell, fromLeft, encode, Arithmetic.pi₁_pair, Arithmetic.pi₂_pair]

theorem reindex_window (w : DecoderWindow) (l r : M) :
    windowCode (translateWindow w) l r = reindex (image w.config.state) (windowCode w l r) := by
  simp only [windowCode, translateWindow, reindex, cell, encode,
    Arithmetic.pi₁_pair, Arithmetic.pi₂_pair]

theorem checkedStep_run (q : Fin 344) (read : Bool) {w : DecoderWindow} {l r left tail : M}
    (state : w.config.state = q.val)
    (start : windowCode w l r = cell q.val left (pushBit read tail))
    (checked : checkStep w = true) :
    let e := transition q read
    Progress machine (cell (image q.val) left (pushBit read tail))
      (if e.right then cell (image e.target) (pushBit e.write left) tail
       else fromLeft (image e.target) left (pushBit e.write tail)) := by
  cases advance : next decoderReference w with
  | none => simp [checkStep, advance] at checked
  | some dst =>
    have matched : verifies w dst 3 = true := by simpa only [checkStep, advance] using checked
    have old := window_tick advance l r
    rw [start] at old
    let e := transition q read
    have row := Decoder.transition_row q read
    have tick := Reaches.tick_of_row (M := M) row.1 row.2 left tail
    change ArithmeticMachine.tick decoderReference.workingStates decoderReference.packedRows
      (cell q.val left (pushBit read tail)) =
        (if e.right then cell e.target (pushBit e.write left) tail
         else fromLeft e.target left (pushBit e.write tail)) at tick
    have result := old.symm.trans tick
    have target : dst.config.state = e.target := by
      have labels := congrArg (π₁ ·) result
      by_cases right : e.right = true
      · simp only [windowCode, right, ↓reduceIte, cell, encode, Arithmetic.pi₁_pair,
          nat_cast_inj] at labels
        exact labels
      · have noRight := Bool.of_not_eq_true right
        simp only [windowCode, noRight, Bool.false_eq_true, ↓reduceIte, fromLeft, encode,
          Arithmetic.pi₁_pair, nat_cast_inj] at labels
        exact labels
    have run := verifies_run matched l r
    rw [reindex_window, reindex_window, state, target, start, result, reindex_cell] at run
    change Progress machine _ (if e.right then _ else _)
    cases direction : e.right
    · simpa only [direction, Bool.false_eq_true, ↓reduceIte, reindex_fromLeft] using run
    · simpa only [direction, ↓reduceIte, reindex_cell] using run

/-- Numerical value of the finite reversed pointer, including its root marker. -/
def leftCode : List Bool → Nat
  | [] => 1
  | bit :: rest => 2 * leftCode rest + bit.toNat

theorem leftCode_cast (before : List Bool) :
    packWord before (1 : M) = (leftCode before : M) := by
  induction before with
  | nil => simp [leftCode]
  | cons bit tail ih =>
    rw [packWord_cons, ih]
    simp only [leftCode, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pushBit]

theorem leftCode_mod (before : List Bool) (bit : Bool) :
    leftCode (bit :: before) % 8 = (2 * (leftCode before % 8) + bit.toNat) % 8 := by
  simp only [leftCode]
  omega

theorem ordinary_run (q : Fin 344) (before : List Bool) (read : Bool) (tail : M)
    (checked : ordinaryCheck q (leftCode before % 8) read = true) :
    let e := transition q read
    let l := packWord before (1 : M)
    Progress machine (cell (image q.val) l (pushBit read tail))
      (if e.right then cell (image e.target) (pushBit e.write l) tail
       else fromLeft (image e.target) l (pushBit e.write tail)) := by
  let w := input q (leftCode before % 8) read
  apply checkedStep_run (w := w) (M := M) (l := ((leftCode before / 2 : Nat) : M)) (r := tail) q read rfl _ checked
  have left : (leftCode before % 8) % 2 + 2 * (leftCode before / 2) = leftCode before := by omega
  have leftTape : (((leftCode before % 8) % 2 : Nat) : M) +
      (2 : M) * ((leftCode before / 2 : Nat) : M) = packWord before 1 := by
    rw [leftCode_cast]
    exact_mod_cast left
  have rightTape : (read.toNat : M) + (2 : M) * tail = pushBit read tail := by
    rw [pushBit, add_comm]
  exact congrArg₂ (cell q.val) leftTape rightTape


/-- The shared owner moves one cell into the gap, which is known to be
zero for this pure control arm, and then returns to the previous exit. -/
theorem removed_run (before : List Bool) (tail : M)
    (checked : continueWordCheck (leftCode before % 8) = true) :
    Progress machine (cell (image 48) (packWord before 1) (pushBit true (pushBit false tail)))
      (fromLeft 8 (packWord before 1) (pushBit false (pushBit false tail))) := by
  let w : DecoderWindow := ⟨⟨48, (leftCode before % 8) % 2, 1⟩, 1, 2⟩
  have check : checkStep w = true := checked
  have left : (leftCode before % 8) % 2 + 2 * (leftCode before / 2) = leftCode before := by omega
  have start : windowCode w ((leftCode before / 2 : Nat) : M) tail =
      cell 48 (packWord before 1) (pushBit true (pushBit false tail)) := by
    have leftTape : (((leftCode before % 8) % 2 : Nat) : M) +
        (2 : M) * ((leftCode before / 2 : Nat) : M) = packWord before 1 := by
      rw [leftCode_cast]
      exact_mod_cast left
    have rightTape : (1 : M) + (4 : M) * tail = pushBit true (pushBit false tail) := by
      simp only [pushBit, Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one, add_zero]
      ring
    refine congrArg₂ (cell 48) leftTape ?_
    simpa [w] using rightTape
  have run := checkedStep_run (M := M) ⟨48,by decide⟩ true rfl start check
  have row : transition 48 true = ⟨8,false,false⟩ := by decide +kernel
  have port : image 8 = 8 := by decide +kernel
  simpa only [row, port, Bool.false_eq_true, ↓reduceIte] using run

theorem packWord_affine (word : List Bool) (tail : M) :
    packWord word tail = (Engine.bits word : M) + ((2 ^ word.length : Nat) : M) * tail := by
  induction word with
  | nil => simp [Engine.bits]
  | cons bit word ih =>
    rw [packWord_cons, ih]
    cases bit <;>
      simp only [Engine.bits, Engine.bit, pushBit, Bool.toNat_false, Bool.toNat_true, Nat.cast_zero,
        Nat.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, List.length_cons, Nat.pow_succ',
        Bool.false_eq_true, ↓reduceIte] <;>
      ring

theorem window_words (q : Nat) (left right : List Bool) (l r : M) :
    windowCode ⟨⟨q, Engine.bits left, Engine.bits right⟩, left.length, right.length⟩ l r =
      cell q (packWord left l) (packWord right r) := by
  simp only [windowCode, cell, packWord_affine]

def donorPrefix (left : Nat) : List Bool :=
  if left % 4 = 3 then [true, true] else [true, false, true]

def donorRight (left : Nat) : List Bool :=
  true :: List.replicate (donorWidth left + 1) false

/-- After the last donor bit, both traces reset the dispatcher at the
first surviving one. The literal reaches that common state directly. -/
theorem donor_run (q left : Nat) (checked : donorCheck q left = true)
    (prefixTail rightTail : M) :
    Progress machine
      (cell (image q) (packWord (donorPrefix left) prefixTail) (pushBit true (pushBit false rightTail)))
      (fromLeft 9 prefixTail (packWord (donorRight left) rightTail)) := by
  have h := checked
  simp only [donorCheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨previous, tail⟩ := pushBit_split prefixTail
  let l := divIn prefixTail 2
  have split : pushBit previous l = prefixTail := tail
  have window := List.all_eq_true.mp h.2 previous (by cases previous <;> simp)
  have certified : verifies (donorInput q left previous) (donorExit left previous) 6 = true := by
    simpa only [Bool.and_eq_true] using (show
      (runToMatch decoderReference (donorExit left previous) (donorSteps left)
          (donorInput q left previous) == some (donorSteps left)) = true ∧
        verifies (donorInput q left previous) (donorExit left previous) 6 = true from
        by simpa only [Bool.and_eq_true] using window).2
  have replay := verifies_run certified l rightTail
  have port : image 9 = 9 := by decide +kernel
  have first : translateWindow (donorInput q left previous) =
      ⟨⟨image q, Engine.bits (donorPrefix left ++ [previous]), 1⟩,
        (donorPrefix left ++ [previous]).length, 2⟩ := by
    by_cases short : left % 4 = 3
    · cases previous <;> simp [translateWindow, donorInput, donorWidth, donorPrefix, short,
        Engine.bits, Engine.bit]
    · have longer := h.1.resolve_left short
      cases previous <;> simp [translateWindow, donorInput, donorWidth, donorPrefix, short, longer,
        Engine.bits, Engine.bit]
  have last : translateWindow (donorExit left previous) =
      ⟨⟨9, 0, Engine.bits (previous :: donorRight left)⟩, 0, (previous :: donorRight left).length⟩ := by
    by_cases short : left % 4 = 3 <;> cases previous <;>
      simp [translateWindow, donorExit, donorWidth, donorRight, short, port, Engine.bits, Engine.bit]
  rw [first, last] at replay
  have source : windowCode
      ⟨⟨image q, Engine.bits (donorPrefix left ++ [previous]), 1⟩,
        (donorPrefix left ++ [previous]).length, 2⟩ l rightTail =
        cell (image q) (packWord (donorPrefix left) prefixTail) (pushBit true (pushBit false rightTail)) := by
    change windowCode
      ⟨⟨image q, Engine.bits (donorPrefix left ++ [previous]), Engine.bits [true,false]⟩,
        (donorPrefix left ++ [previous]).length, ([true,false] : List Bool).length⟩ l rightTail = _
    rw [window_words, packWord_append, packWord_cons, packWord_nil, split]
    rfl
  have target : windowCode
      ⟨⟨9, 0, Engine.bits (previous :: donorRight left)⟩, 0, (previous :: donorRight left).length⟩ l rightTail =
        fromLeft 9 prefixTail (packWord (donorRight left) rightTail) := by
    change windowCode ⟨⟨9, Engine.bits [], Engine.bits (previous :: donorRight left)⟩,
      ([] : List Bool).length, (previous :: donorRight left).length⟩ l rightTail = _
    rw [window_words, packWord_nil, packWord_cons, ← split, fromLeft_pushBit]
    rfl
  simpa only [source, target] using replay


end PalomarI3334.LiteralDecoder
