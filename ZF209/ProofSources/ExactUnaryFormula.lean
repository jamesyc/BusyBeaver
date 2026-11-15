module
public import UnaryRuleFormulaTemplate
public import ExactContextSubDefinability
public import ExactSourceSubstNat
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def unaryFormula : 𝚺ᴬ₁.Semisentence 2 := unaryFormulaWith contextSubFormula
def modelUnary (p r : M) := modelUnaryWith modelContextSub p r
lemma unaryFormula_defined : 𝚺ᴬ₁.DefinedRel (modelUnary (M:=M)) unaryFormula :=
 unaryFormulaWith_defined contextSubFormula modelContextSub contextSubFormula_defined
lemma unaryFormula_eval (p r : M) : unaryFormula.val.Evalb ![p,r] ↔ modelUnary p r := unaryFormula_defined.iff
lemma unaryFormula_nat (p r : Nat) : unaryFormula.val.Evalb ![p,r] ↔ sourceUnary p r := by
 rw [unaryFormula_eval]
 simp only [modelUnary,modelUnaryWith,sourceUnary,modelRowWf_nat,modelSequent_nat,modelSourceNode_nat,modelSourceContextShift_nat,modelSourceSubst_nat,modelContextSub_nat,modelListCons,modelCantor_nat,sourceCons]
 rfl
end ZFR.ArithmeticRepresentation
