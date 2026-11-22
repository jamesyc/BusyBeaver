module
public import ZF192.Tape.Reachability
public import ZF192.Tape.BitRuns
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Read the two sides in the order (destination, source), with a fixed head bit for left scans. -/
def scanState (q : Nat) (b right : Bool) (dst src : M) : State M :=
  if right then ⟨(q : M), dst, src⟩ else ⟨(q : M), src, bitValue b + 2 * dst⟩

def scanStateGraph (q : Nat) (b right : Bool) : ArithmeticSemisentence 3 :=
  if right then “z dst src. !stateGraph z ↑q dst src”
  else “z dst src. !stateGraph z ↑q src (↑(boolNat b) + 2 * dst)”

theorem scanStateGraph_eval (q : Nat) (b right : Bool) (z dst src : M) :
    (scanStateGraph q b right).Evalb ![z, dst, src] ↔ z = stateCode (scanState q b right dst src) := by
  cases right <;>
    simp [scanStateGraph, scanState, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons',
      Empty.eq_elim, Matrix.empty_eq, Matrix.constant_eq_singleton, stateGraph_eval,
      numeral_eq_natCast, boolNat_cast]

def Scan (q : Nat) (b right : Bool) (n : M) : Prop :=
  ∀ dst src, Reaches (scanState q b right dst (bitRun n (bitValue b) src))
    (scanState q b right (bitRun n (bitValue b) dst) src)

def scanFormula (q : Nat) (b right : Bool) : ArithmeticSemiformula Nat 1 :=
  let state := scanStateGraph q b right
  let bit := boolNat b
  “n. ∀dst, ∀src, ∀initial, ∀hist, ∀s, ∀t, ∀before, ∀after,
   !bitRunGraph s n ↑bit src → !bitRunGraph t n ↑bit dst →
   !state before dst s → !state after t src →
   !physicalRunFormula initial hist → !listHeadGraph before hist →
   ∃out, !physicalRunFormula initial out ∧ !listHeadGraph after out”

theorem scanFormula_eval (ρ : Nat → M) (q : Nat) (b right : Bool) (n : M) :
    (scanFormula q b right).Eval ![n] ρ ↔ Scan q b right n := by
  simp [scanFormula, Scan, Reaches, Semiformula.eval_rew, Function.comp_def,
    Matrix.comp_vecCons', Matrix.empty_eq, Empty.eq_elim, Matrix.constant_eq_singleton,
    bitRun_defined.iff, scanStateGraph_eval, physicalRunFormula_eval, ruleHead_defined.iff,
    numeral_eq_natCast, boolNat_cast, eq_comm]
  constructor
  · intro h dst src initial hist hh he
    obtain ⟨out, ho, hend⟩ := h dst src initial hist _ _ _ _ rfl rfl rfl rfl hh he
    exact ⟨out, ho, hend⟩
  · intro h dst src initial hist s t before after hs ht hb ha hh he
    rw [hs] at hb
    rw [ht] at ha
    obtain ⟨out, ho, hend⟩ := h dst src initial hist hh (hb.symm.trans he)
    exact ⟨out, ho, ha.trans hend⟩

private theorem scan_step (q : Nat) (b right : Bool) (dst src : M)
    (row : M192.literal q b = some (b, right, q)) :
    literalStep (scanState q b right dst (bitValue b + 2 * src))
      (scanState q b right (bitValue b + 2 * dst) src) := by
  cases right
  · have four : (2 : M) * 2 = 4 := by norm_num
    simpa only [scanState, Bool.false_eq_true, ite_false, mul_add, ← mul_assoc, four, add_assoc] using
      physical_left q q b b b src dst row
  · simpa [scanState] using physical_right q q b b dst src row

/-- A preserving self-loop scans any model length in its direction of motion. -/
theorem physical_scan (q : Nat) (b right : Bool) (row : M192.literal q b = some (b, right, q)) :
    ∀ n : M, Scan q b right n := by
  have : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔)
  refine InductionScheme.succ_induction (C := Set.univ) (P := Scan q b right) ?_ ?_ ?_
  · exact ⟨(fun _ => 0), scanFormula q b right, by trivial,
      fun n => (scanFormula_eval (fun _ => 0) q b right n).symm⟩
  · intro dst src
    simp only [bitRun_zero]
    exact Reaches.refl _
  · intro n ih dst src
    have step := Reaches.step (scan_step q b right dst (bitRun n (bitValue b) src) row)
    rw [← bitRun_succ] at step
    simpa only [bitRun_commute] using step.trans (ih (bitValue b + 2 * dst) src)

lemma scan_right (q : Nat) (b : Bool) (n l r : M)
    (row : M192.literal q b = some (b, true, q)) :
    Reaches ⟨(q : M), l, bitRun n (bitValue b) r⟩ ⟨(q : M), bitRun n (bitValue b) l, r⟩ :=
  physical_scan q b true row n l r

lemma physical_scan_left (q : Nat) (b : Bool)
    (row : M192.literal q b = some (b, false, q)) (n l r : M) :
    Reaches ⟨(q : M), bitRun n (bitValue b) l, bitValue b + 2 * r⟩
      ⟨(q : M), l, bitRun n (bitValue b) (bitValue b + 2 * r)⟩ := by
  have h : bitValue b + 2 * bitRun n (bitValue b) r =
      bitRun n (bitValue b) (bitValue b + 2 * r) := by
    rw [bitRun_commute, bitRun_succ]
  simpa only [scanState, Bool.false_eq_true, ite_false, h] using physical_scan q b false row n r l

end ZF192.BinaryTape
