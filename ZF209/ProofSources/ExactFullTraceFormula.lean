module
public import ExactTraceNat
public import ExactFullRuleFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma modelFullRules_nat (r xs : Nat) : modelFullRules r xs ↔ sourceFullRules r xs := by
 have hu (p r : Nat) : modelUnary p r ↔ sourceUnary p r := (unaryFormula_eval p r).symm.trans (unaryFormula_nat p r)
 have hb (r : Nat) : modelBase r ↔ sourceBase r := (baseFormula_eval r).symm.trans (baseFormula_nat r)
 have hbi (p q r : Nat) : modelBinary p q r ↔ sourceBinary p q r := (binaryFormula_eval p q r).symm.trans (binaryFormula_nat p q r)
 simp only [modelFullRules,sourceFullRules,hu,hb,hbi,modelMember_nat]
def fullTraceFormula : 𝚺ᴬ₁.Semisentence 1 := traceFormula fullRuleFormula
lemma fullTraceFormula_defined : 𝚺ᴬ₁.DefinedPred (modelTrace (modelFullRules (M:=M))) fullTraceFormula :=
 traceFormula_defined fullRuleFormula modelFullRules fullRuleFormula_defined
end ZFR.ArithmeticRepresentation
