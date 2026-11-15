module
public import ExactContextSubCodeGraph
public import ExactMemberPredicate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def contextSubFormula : 𝚺ᴬ₁.Semisentence 2 := memberOutputOne contextSubCodeGraph

lemma contextSubFormula_eval (x n : M) : contextSubFormula.val.Evalb ![x,n] ↔ modelContextSub x n := by
 change (memberOutputOne contextSubCodeGraph).val.Evalb ![x,n] ↔ modelContextSubCode x n=1
 rw [memberOutputOne_eval,contextSubCodeGraph_eval]
 exact eq_comm

end ZFR.ArithmeticRepresentation
