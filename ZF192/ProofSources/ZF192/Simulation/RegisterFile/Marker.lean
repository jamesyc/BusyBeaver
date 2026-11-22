module
public import ZF192.Simulation.RegisterFile.Operations
public import ZF192Support.Coding.Arithmetic.FormulaCertificates
@[expose] public section

/-! # The moving tape marker

The least significant bits below are nearest the head. A successful update
runs right in state `retS`, with a zero marker immediately left of the head.
Each short path moves the unprocessed part of the file one cell left. The
two adjacent gate zeros end the return. -/
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano M192
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

abbrev b0 (x : M) := 2*x
abbrev b1 (x : M) := 1+2*x

local instance : Trans (Reaches (M := M)) Reaches Reaches := ⟨Reaches.trans⟩

/-- Copy a body cell past the pending marker. -/
lemma marker_one (l r : M) :
    Reaches (cell retS (b0 l) (b1 r)) (cell retS (b0 (b1 l)) r) := by
  calc
    Reaches (cell retS (b0 l) (b1 r)) (cell retS l (b0 (b1 r))) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add, cellL_zero, cellL_one] using stepL1 row_retS_1 (b0 l) r
    Reaches _ (cell gateArith (b0 l) (b1 r)) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using stepR0 row_retS_0 l (b1 r)
    Reaches _ (cell copy1 l (b0 (b1 r))) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add, cellL_zero, cellL_one] using stepL1 row_gateArith_1 (b0 l) r
    Reaches _ (cell delTest (b1 l) (b1 r)) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using stepR0 row_copy1_0 l (b1 r)
    Reaches _ (cell retS (b0 (b1 l)) r) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using stepR1 row_delTest_1 (b1 l) r

/-- Copy a separator and the adjacent body cell. -/
lemma marker_separator (l r : M) :
    Reaches (cell retS (b0 l) (b0 (b1 r))) (cell retS (b0 (b1 (b0 l))) r) := by
  calc
    Reaches (cell retS (b0 l) (b0 (b1 r))) (cell gateArith (b0 (b0 l)) (b1 r)) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR0 row_retS_0 (b0 l) (b1 r)
    Reaches _ (cell copy1 (b0 l) (b0 (b1 r))) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add, cellL_zero, cellL_one] using
        stepL1 row_gateArith_1 (b0 (b0 l)) r
    Reaches _ (cell delTest (b1 (b0 l)) (b1 r)) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR0 row_copy1_0 (b0 l) (b1 r)
    Reaches _ (cell retS (b0 (b1 (b0 l))) r) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR1 row_delTest_1 (b1 (b0 l)) r

/-- At the old gate, turn its program-side cell into padding. -/
lemma marker_gate (l r : M) :
    Reaches (cell retS (b0 l) (b0 (b0 (b1 r)))) (cell readSuccess (b1 (b0 (b0 l))) (b1 r)) := by
  calc
    Reaches (cell retS (b0 l) (b0 (b0 (b1 r)))) (cell gateArith (b0 (b0 l)) (b0 (b1 r))) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR0 row_retS_0 (b0 l) (b0 (b1 r))
    Reaches _ (cell readSuccess (b1 (b0 (b0 l))) (b1 r)) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR0 row_gateArith_0 (b0 (b0 l)) (b1 r)

/-- The carry detour writes the separator and resumes the forward copy. -/
lemma copy1_body (l r : M) :
    Reaches (cell copy1 l (b1 (b1 r))) (cellL copy0 l (b0 (b1 r))) := by
  simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using stepL1 row_copy1_1 l (b1 r)

/-- Prepare the pending marker at the last active separator. -/
lemma copy1_cap_bit (l r : M) :
    Reaches (cell copy1 (b0 l) (b0 (b1 r))) (cell retS (b0 (b1 (b0 l))) r) := by
  calc
    Reaches (cell copy1 (b0 l) (b0 (b1 r))) (cell delTest (b1 (b0 l)) (b1 r)) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR0 row_copy1_0 (b0 l) (b1 r)
    Reaches _ (cell retS (b0 (b1 (b0 l))) r) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR1 row_delTest_1 (b1 (b0 l)) r

/-- On an isolated separator, resume the zero return on the adjacent body cell. -/
lemma zero_cross_separator (l r : M) :
    Reaches (cell retZ l (b0 (b1 r))) (cell retZ (b0 l) (b1 r)) := by
  calc
    Reaches (cell retZ l (b0 (b1 r))) (cell delBegin (b0 l) (b1 r)) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR0 row_retZ_0 l (b1 r)
    Reaches _ (cell delTest l (b0 (b1 r))) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add, cellL_zero, cellL_one] using
        stepL1 row_delBegin_1 (b0 l) r
    Reaches _ (cell retZ (b0 l) (b1 r)) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR0 row_delTest_0 l (b1 r)

/-- Two adjacent zeros end the zero return. -/
lemma zero_gate (l r : M) :
    Reaches (cell retZ l (b0 (b0 r))) (cell readZero (b0 (b0 l)) r) := by
  calc
    Reaches (cell retZ l (b0 (b0 r))) (cell delBegin (b0 l) (b0 r)) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR0 row_retZ_0 l (b0 r)
    Reaches _ (cell readZero (b0 (b0 l)) r) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR0 row_delBegin_0 (b0 l) r

/-- A zero test starts the zero return. -/
lemma dec_zero_begin (l r : M) :
    Reaches (cell delBegin (b0 l) (b1 r)) (cell retZ (b1 (b0 l)) r) := by
  calc
    Reaches (cell delBegin (b0 l) (b1 r)) (cell delTest l (b0 (b1 r))) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add, cellL_zero, cellL_one] using
        stepL1 row_delBegin_1 (b0 l) r
    Reaches _ (cell retZ (b0 l) (b1 r)) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR0 row_delTest_0 l (b1 r)
    Reaches _ (cell retZ (b1 (b0 l)) r) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using
        stepR1 row_retZ_1 (b0 l) r

/-- For a positive decrement, mark the compulsory first body cell. -/
lemma dec_plant (l r : M) :
    Reaches (cell delBegin (b1 l) (b1 r)) (cell retS (b0 (b1 l)) r) := by
  calc
    Reaches (cell delBegin (b1 l) (b1 r)) (cell delTest l (b1 (b1 r))) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add, cellL_zero, cellL_one] using stepL1 row_delBegin_1 (b1 l) r
    Reaches _ (cell retS (b0 l) (b1 r)) := by
      simpa only [bitValue, Bool.false_eq_true, ite_false, ite_true, zero_add] using stepR1 row_delTest_1 l (b1 r)
    Reaches _ (cell retS (b0 (b1 l)) r) := marker_one l r

/-! The number of body cells in a register may be nonstandard. Express the
marker scan as a first-order predicate and apply induction in the PA model. -/

private def markerScanFormula : ArithmeticSemiformula Nat 1 :=
 “n. ∀l, ∀r, ∀initial, ∀hist, ∀right, ∀left, ∀before, ∀after,
 !bitRunGraph right n 1 r → !bitRunGraph left n 1 l →
 !stateGraph before ↑retS (2*l) right → !stateGraph after ↑retS (2*left) r →
 !physicalRunFormula initial hist → !listHeadGraph before hist →
 ∃out, !physicalRunFormula initial out ∧ !listHeadGraph after out”

private def MarkerScan (n : M) : Prop :=
  ∀ l r : M, Reaches (cell retS (b0 l) (ones n r)) (cell retS (b0 (ones n l)) r)

private lemma markerScan_eval (n : M) :
    markerScanFormula.Eval ![n] (fun _ => (0 : M)) ↔ MarkerScan n := by
  simp [markerScanFormula, MarkerScan, Reaches, cell, ones, Semiformula.eval_rew,
    Function.comp_def, Matrix.comp_vecCons', Matrix.empty_eq, Empty.eq_elim, Matrix.constant_eq_singleton,
    bitRun_defined.iff, stateGraph_eval, physicalRunFormula_eval, ruleHead_defined.iff,
    numeral_eq_natCast]
  constructor
  · intro h l r initial hist hh he
    obtain ⟨out, ho, hend⟩ := h l r initial hist _ _ _ _ rfl rfl rfl rfl hh he.symm
    exact ⟨out, ho, hend.symm⟩
  · intro h l r initial hist right left before after hr hl hb ha hh he
    rw [hr] at hb
    rw [hl] at ha
    obtain ⟨out, ho, hend⟩ := h l r initial hist hh (he.symm.trans hb)
    exact ⟨out, ho, ha.trans hend.symm⟩

lemma marker_scan (n : M) (l r : M) :
    Reaches (cell retS (b0 l) (ones n r)) (cell retS (b0 (ones n l)) r) := by
  suffices h : MarkerScan n from h l r
  clear l r
  let cert : FormulaCertificate (fun _ => (0 : M)) 1 (fun v => MarkerScan (v 0)) :=
    ⟨markerScanFormula, fun v => by
      rw [Matrix.fun_eq_vec_one v]
      exact (markerScan_eval _).symm⟩
  apply cert.induction
  · change MarkerScan (0 : M)
    intro l r
    simpa only [ones_zero] using Reaches.refl (cell retS (b0 l) r)
  · intro k ih
    change MarkerScan k at ih
    change MarkerScan (k+1)
    intro l r
    rw [ones_succ k r, ← ones_commute k l]
    exact (marker_one l (ones k r)).trans (ih (b1 l) r)

/-- Cross the right-facing image of a complete earlier register. -/
lemma marker_cross (v l r : M) :
    Reaches (cell retS (b0 l) (rblk v r)) (cell retS (b0 (blk v l)) r) := by
  rw [rblk_eq, blk_eq]
  refine (marker_separator l (ones v r)).trans ?_
  have h := marker_scan v (b1 (b0 l)) r
  rwa [ones_commute, ones_succ] at h

lemma marker_blocks (pre : List M) (l r : M) :
    Reaches (cell retS (b0 l) (revPush pre r)) (cell retS (b0 (file pre l)) r) := by
  induction pre generalizing r with
  | nil => exact Reaches.refl _
  | cons v pre ih =>
    rw [revPush, file_cons]
    exact (ih (rblk v r)).trans (marker_cross v (file pre l) r)

end ZF192.BinaryTape
