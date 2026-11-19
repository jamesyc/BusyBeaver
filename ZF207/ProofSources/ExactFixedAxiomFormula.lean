module
public import ExactFixedFormulaGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
def fixedFormulaListGraph : List Formula → 𝚺ᴬ₁.Semisentence 1
 | [] => .mkSigma “z. 0=1”
 | f::fs => .mkSigma “z. !(fixedFormulaGraph f) z ∨ !(fixedFormulaListGraph fs) z”
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma fixedFormulaListGraph_eval (fs : List Formula) (z : M) :
 (fixedFormulaListGraph fs).val.Evalb ![z] ↔ ∃f∈fs,z=modelFixedFormula f := by
 induction fs with
 | nil => simp [fixedFormulaListGraph]
 | cons f fs ih =>
  simp [fixedFormulaListGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.empty_eq]
  rw [fixedFormulaGraph_eval,ih]

def fixedAxiomList : List Formula := [fixedRefl,fixedSym,fixedTrans,fixedEqElem,fixedExt,
 fixedEmpty,fixedPair,fixedUnion,fixedPower,fixedOmega,fixedFoundation]
def fixedAxiomFormula : 𝚺ᴬ₁.Semisentence 1 := fixedFormulaListGraph fixedAxiomList
def modelFixedAxiom (z : M) := ∃f∈fixedAxiomList,z=modelFixedFormula f
lemma fixedAxiomFormula_defined : 𝚺ᴬ₁.DefinedPred (modelFixedAxiom (M:=M)) fixedAxiomFormula := .mk (by
 intro v
 have hv : v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact fixedFormulaListGraph_eval _ _)
lemma fixedAxiomFormula_nat (z : Nat) : fixedAxiomFormula.val.Evalb ![z] ↔ sourceZfrFixed z := by
 rw [fixedAxiomFormula,fixedFormulaListGraph_eval]
 simp [modelFixedFormula_nat,fixedAxiomList,sourceZfrFixed]
end ZFR.ArithmeticRepresentation
