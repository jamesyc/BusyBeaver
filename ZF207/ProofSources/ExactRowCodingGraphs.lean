module
public import ExactContextWfSentences
public import ExactContextShiftSentences
public import ExactSourceBoundEquations
public import ExactSourceShiftSentences
public import ExactSourceSubstSentences
public import ExactListDecoderGraphs
public import ExactMemberNat
public import ExactMemberPredicate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma rowCantor_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelCantor (M := M)) exactCantorGraph := .mk (by
 intro v
 simp only [exactCantorGraph]
 simp
 change 2*v 0=(v 1+v 2)*((v 1+v 2)+1)+2*v 2 ↔ v 0=modelCantor (v 1) (v 2)
 exact ⟨modelCantor_unique _ _ _,fun h => h ▸ modelCantor_equation _ _⟩)
noncomputable def modelSequent (g a : M) := modelCantor 0 (modelCantor g a)
noncomputable def modelBranches (g a b c : M) := modelCantor 1 (modelCantor g (modelCantor a (modelCantor b c)))
def sequentGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “r g a. ∃ u, !exactCantorGraph u g a ∧ !exactCantorGraph r 0 u”
def branchesGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
 “r g a b c. ∃ u, ∃ v, ∃ w, !exactCantorGraph u b c ∧ !exactCantorGraph v a u ∧ !exactCantorGraph w g v ∧ !exactCantorGraph r 1 w”
lemma sequentGraph_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelSequent (M := M)) sequentGraph := .mk (by
 intro v
 simp [sequentGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,rowCantor_defined.iff,modelSequent])
lemma modelSequent_nat (g a : Nat) : modelSequent g a=sourceSequent g a := by simp [modelSequent,sourceSequent,modelCantor_nat]
lemma modelBranches_nat (g a b c : Nat) : modelBranches g a b c=sourceBranches g a b c := by simp [modelBranches,sourceBranches,modelCantor_nat]
end ZFR.ArithmeticRepresentation
