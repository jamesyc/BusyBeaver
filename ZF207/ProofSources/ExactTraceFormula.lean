module
public import ExactTailIteration
public import NumericTrace
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma ruleHead_defined : 𝚺ᴬ₁.DefinedFunction₁ (modelListHead (M:=M)) listHeadGraph := .mk (by
 intro v
 have hv : v=![v 0,v 1] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]; exact listHeadGraph_eval _ _)
/-- Bounded universal closure of a positive Sigma1 relation; no truth-indicator. -/
def traceFormula (rel : 𝚺ᴬ₁.Semisentence 2) : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
 “n. !tailIterationGraph 0 n n ∧ ∀ k<n, ∃ g, !tailIterationGraph g k n ∧
 (g=0 ∨ ∃ a, ∃ b, !listHeadGraph a g ∧ !listTailGraph b g ∧ !rel a b)”
def modelTrace (rel : M → M → Prop) (n : M) : Prop := modelTailIter n n=0 ∧
 ∀ k<n, modelTailIter k n=0 ∨ rel (modelListHead (modelTailIter k n)) (modelListTail (modelTailIter k n))
lemma traceFormula_defined (rel : 𝚺ᴬ₁.Semisentence 2) (R : M → M → Prop) (hR : 𝚺ᴬ₁.DefinedRel R rel) :
 𝚺ᴬ₁.DefinedPred (modelTrace R) (traceFormula rel) := .mk (by
 intro v
 simp [traceFormula,modelTrace,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,
 tailIterationGraph_defined.iff,ruleHead_defined.iff,ruleTail_defined.iff,hR.iff,eq_comm])
end ZFR.ArithmeticRepresentation
