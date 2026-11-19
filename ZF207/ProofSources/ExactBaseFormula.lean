module
public import ExactRowWfFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma ruleNode_defined : 𝚺ᴬ₁.DefinedFunction₃ (modelSourceNode (M := M)) sourceNodeGraph := .mk (by
 intro v
 simp [sourceNodeGraph,modelCantor_defined.iff,modelSourceNode,numeral_eq_natCast])
lemma ruleMember_defined : 𝚺ᴬ₁.DefinedRel (modelMember (M := M)) memberFormula := .mk (by
 intro v
 have hv : v=![v 0,v 1] := by
   funext j; refine Fin.cases ?_ (fun j => ?_) j
   · rfl
   · have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 rw [hv]; exact memberFormula_eval _ _)
def baseFormula : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
 “r. !rowWfFormula r ∧
 ((∃ g, ∃ a, !sequentGraph r g a ∧ !memberFormula a g) ∨
 (∃ g, ∃ a, ∃ b, ∃ u, ∃ v, ∃ w,
 !sourceNodeGraph u 5 a b ∧ !sourceNodeGraph v 5 u a ∧ !sourceNodeGraph w 5 v a ∧ !sequentGraph r g w))”
def modelBase (r : M) := modelRowWf r ∧
 ((∃ g a, r=modelSequent g a ∧ modelMember a g) ∨
  ∃ g a b, r=modelSequent g (modelSourceNode 5 (modelSourceNode 5 (modelSourceNode 5 a b) a) a))
lemma baseFormula_defined : 𝚺ᴬ₁.DefinedPred (modelBase (M:=M)) baseFormula := .mk (by
 intro v
 simp [baseFormula,modelBase,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,
 rowWfFormula_defined.iff,sequentGraph_defined.iff,ruleMember_defined.iff,ruleNode_defined.iff,numeral_eq_natCast])
lemma baseFormula_eval (r : M) : baseFormula.val.Evalb ![r] ↔ modelBase r := baseFormula_defined.iff
lemma baseFormula_nat (r : Nat) : baseFormula.val.Evalb ![r] ↔ sourceBase r := by
 rw [baseFormula_eval]
 simp only [modelBase,sourceBase,modelRowWf_nat,modelSequent_nat,modelMember_nat,modelSourceNode_nat]
 rfl
end ZFR.ArithmeticRepresentation
