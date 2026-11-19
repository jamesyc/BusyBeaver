module
public import ExactUnaryFormula
public import ExactBinaryFormula
public import ExactSourceDerives
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def fullRuleFormula : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “r xs. !baseFormula r ∨ (∃ p, !memberFormula p xs ∧ !unaryFormula p r) ∨
 (∃ p, ∃ q, !memberFormula p xs ∧ !memberFormula q xs ∧ !binaryFormula p q r)”
def modelFullRules (r xs : M) :=
 modelBase r ∨ (∃ p,modelMember p xs ∧ modelUnary p r) ∨
 ∃ p q,modelMember p xs ∧ modelMember q xs ∧ modelBinary p q r
lemma fullRuleFormula_defined : 𝚺ᴬ₁.DefinedRel (modelFullRules (M := M)) fullRuleFormula := .mk (by
 intro v
 simp [fullRuleFormula,modelFullRules,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
 Matrix.comp_vecCons',Matrix.empty_eq,baseFormula_defined.iff,memberFormula_defined.iff,
 unaryFormula_defined.iff,binaryFormula_defined.iff])
end ZFR.ArithmeticRepresentation
