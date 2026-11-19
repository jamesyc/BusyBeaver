module
public import ExactSourceWfSentences
public import ExactSourceShiftSentences
public import SourceBoundByShift
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def sourceBoundFormula : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “k n. !sourceWfFormula n ∧ !sourceShiftGraph n k n”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def modelSourceBound (k n : M) : Prop := modelSourceWf n ∧ modelSourceShift k n=n

lemma sourceBoundFormula_eval (k n : M) :
 sourceBoundFormula.val.Evalb ![k,n] ↔ modelSourceBound k n := by
 simp [sourceBoundFormula,modelSourceBound,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',sourceWfFormula_defined.iff,sourceShiftGraph_defined.iff,eq_comm]

lemma sourceBoundFormula_defined : 𝚺ᴬ₁.DefinedRel (modelSourceBound (M := M)) sourceBoundFormula := .mk (by
 intro v
 have hv : v=![v 0,v 1] := by funext i; refine Fin.cases rfl (fun j => ?_) i; exact Fin.cases rfl (fun x => Fin.elim0 x) j
 rw [hv]
 exact sourceBoundFormula_eval _ _)

instance modelSourceBound_definable : 𝚺ᴬ₁-Relation (modelSourceBound (M := M)) :=
 sourceBoundFormula_defined.to_definable

lemma modelSourceBound_zero (k : M) : modelSourceBound k 0 :=
 ⟨modelSourceWf_zero,modelSourceShift_zero k⟩

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma modelSourceBound_nat (k n : Nat) : modelSourceBound k n ↔ sourceBound k n := by
 rw [sourceBound_iff_shift_fixed]
 simp only [modelSourceBound,modelSourceWf_nat,modelSourceShift_nat]

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma sourceBoundFormula_nat (k n : Nat) : sourceBoundFormula.val.Evalb ![k,n] ↔ sourceBound k n := by
 rw [sourceBoundFormula_eval,modelSourceBound_nat]

end ZFR.ArithmeticRepresentation
