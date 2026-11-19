module
public import ExactBaseFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma ruleCons_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelListCons (M:=M)) listConsGraph := .mk (by
 intro v; simp [listConsGraph,modelCantor_defined.iff,modelListCons])
def binaryFormula : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “p q r. !rowWfFormula r ∧ (
 (∃ g, ∃ a, ∃ b, ∃ u, !sourceNodeGraph u 5 a b ∧ !sequentGraph r g b ∧ !sequentGraph p g u ∧ !sequentGraph q g a) ∨
 (∃ g, ∃ a, ∃ b, ∃ u, !sourceNodeGraph u 3 a b ∧ !sequentGraph r g u ∧ !sequentGraph p g a ∧ !sequentGraph q g b) ∨
 (∃ g, ∃ a, ∃ b, ∃ c, ∃ u, ∃ v, !listConsGraph u a g ∧ !listConsGraph v b g ∧ !branchesGraph r g a b c ∧ !sequentGraph p u c ∧ !sequentGraph q v c) ∨
 (∃ g, ∃ a, ∃ b, ∃ c, ∃ u, !sourceNodeGraph u 4 a b ∧ !sequentGraph r g c ∧ !sequentGraph p g u ∧ !branchesGraph q g a b c) ∨
 (∃ g, ∃ a, ∃ c, ∃ u, ∃ v, ∃ w, ∃ x, !sourceNodeGraph u 7 a 0 ∧ !sourceContextShiftGraph v g ∧ !listConsGraph w a v ∧ !sourceShiftGraph x 0 c ∧ !sequentGraph r g c ∧ !sequentGraph p g u ∧ !sequentGraph q w x))”
def modelBinary (p q r : M) := modelRowWf r ∧ (
 (∃ g a b, r=modelSequent g b ∧ p=modelSequent g (modelSourceNode 5 a b) ∧ q=modelSequent g a) ∨
 (∃ g a b, r=modelSequent g (modelSourceNode 3 a b) ∧ p=modelSequent g a ∧ q=modelSequent g b) ∨
 (∃ g a b c, r=modelBranches g a b c ∧ p=modelSequent (modelListCons a g) c ∧ q=modelSequent (modelListCons b g) c) ∨
 (∃ g a b c, r=modelSequent g c ∧ p=modelSequent g (modelSourceNode 4 a b) ∧ q=modelBranches g a b c) ∨
 (∃ g a c, r=modelSequent g c ∧ p=modelSequent g (modelSourceNode 7 a 0) ∧ q=modelSequent (modelListCons a (modelSourceContextShift g)) (modelSourceShift 0 c)))
lemma binaryFormula_defined : 𝚺ᴬ₁.Defined (fun v : Fin 3 → M => modelBinary (v 0) (v 1) (v 2)) binaryFormula := .mk (by
 intro v
 simp [binaryFormula,modelBinary,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,
 rowWfFormula_defined.iff,sequentGraph_defined.iff,branchesGraph_defined.iff,ruleNode_defined.iff,ruleCons_defined.iff,sourceContextShiftGraph_defined.iff,sourceShiftGraph_defined.iff,numeral_eq_natCast])
lemma binaryFormula_eval (p q r : M) : binaryFormula.val.Evalb ![p,q,r] ↔ modelBinary p q r := binaryFormula_defined.iff
lemma binaryFormula_nat (p q r : Nat) : binaryFormula.val.Evalb ![p,q,r] ↔ sourceBinary p q r := by
 rw [binaryFormula_eval]
 simp only [modelBinary,sourceBinary,modelRowWf_nat,modelSequent_nat,modelBranches_nat,modelSourceNode_nat,modelSourceContextShift_nat,modelSourceShift_nat,modelListCons,modelCantor_nat,sourceCons]
 rfl
end ZFR.ArithmeticRepresentation
