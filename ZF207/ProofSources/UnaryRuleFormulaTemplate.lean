module
public import ExactBinaryFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Syntax composition only; exact weakening predicate is an explicit argument. -/
def unaryFormulaWith (sub : 𝚺ᴬ₁.Semisentence 2) : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “p r. !rowWfFormula r ∧ (
 (∃ g, ∃ a, ∃ b, ∃ u, ∃ v, !sourceNodeGraph u 5 a b ∧ !listConsGraph v a g ∧ !sequentGraph r g u ∧ !sequentGraph p v b) ∨
 (∃ g, ∃ a, !sequentGraph r g a ∧ !sequentGraph p g 0) ∨
 (∃ g, ∃ a, ∃ b, ∃ u, !sourceNodeGraph u 3 a b ∧ !sequentGraph r g a ∧ !sequentGraph p g u) ∨
 (∃ g, ∃ a, ∃ b, ∃ u, !sourceNodeGraph u 3 a b ∧ !sequentGraph r g b ∧ !sequentGraph p g u) ∨
 (∃ g, ∃ a, ∃ b, ∃ u, !sourceNodeGraph u 4 a b ∧ !sequentGraph r g u ∧ !sequentGraph p g a) ∨
 (∃ g, ∃ a, ∃ b, ∃ u, !sourceNodeGraph u 4 a b ∧ !sequentGraph r g u ∧ !sequentGraph p g b) ∨
 (∃ g, ∃ h, ∃ a, !sequentGraph r h a ∧ !sequentGraph p g a ∧ !sub g h) ∨
 (∃ g, ∃ a, ∃ u, ∃ v, !sourceNodeGraph u 6 a 0 ∧ !sourceContextShiftGraph v g ∧ !sequentGraph r g u ∧ !sequentGraph p v a) ∨
 (∃ g, ∃ a, ∃ t, ∃ u, ∃ v, !sourceNodeGraph u 6 a 0 ∧ !sourceSubstGraph v 0 t a ∧ !sequentGraph r g v ∧ !sequentGraph p g u) ∨
 (∃ g, ∃ a, ∃ t, ∃ u, ∃ v, !sourceNodeGraph u 7 a 0 ∧ !sourceSubstGraph v 0 t a ∧ !sequentGraph r g u ∧ !sequentGraph p g v))”
def modelUnaryWith (sub : M → M → Prop) (p r : M) := modelRowWf r ∧ (
 (∃ g a b, r=modelSequent g (modelSourceNode 5 a b) ∧ p=modelSequent (modelListCons a g) b) ∨
 (∃ g a, r=modelSequent g a ∧ p=modelSequent g 0) ∨
 (∃ g a b, r=modelSequent g a ∧ p=modelSequent g (modelSourceNode 3 a b)) ∨
 (∃ g a b, r=modelSequent g b ∧ p=modelSequent g (modelSourceNode 3 a b)) ∨
 (∃ g a b, r=modelSequent g (modelSourceNode 4 a b) ∧ p=modelSequent g a) ∨
 (∃ g a b, r=modelSequent g (modelSourceNode 4 a b) ∧ p=modelSequent g b) ∨
 (∃ g h a, r=modelSequent h a ∧ p=modelSequent g a ∧ sub g h) ∨
 (∃ g a, r=modelSequent g (modelSourceNode 6 a 0) ∧ p=modelSequent (modelSourceContextShift g) a) ∨
 (∃ g a t, r=modelSequent g (modelSourceSubst 0 t a) ∧ p=modelSequent g (modelSourceNode 6 a 0)) ∨
 (∃ g a t, r=modelSequent g (modelSourceNode 7 a 0) ∧ p=modelSequent g (modelSourceSubst 0 t a)))
lemma unaryFormulaWith_defined (sub : 𝚺ᴬ₁.Semisentence 2) (rel : M → M → Prop)
 (hs : 𝚺ᴬ₁.DefinedRel rel sub) : 𝚺ᴬ₁.DefinedRel (modelUnaryWith rel) (unaryFormulaWith sub) := .mk (by
 intro v
 simp [unaryFormulaWith,modelUnaryWith,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,
 rowWfFormula_defined.iff,sequentGraph_defined.iff,ruleNode_defined.iff,ruleCons_defined.iff,sourceContextShiftGraph_defined.iff,sourceSubstGraph_defined.iff,hs.iff,numeral_eq_natCast])
end ZFR.ArithmeticRepresentation
