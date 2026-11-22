module
public import ZF192Support.Coding.Lists.MemberPredicate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma memberCodeGraph_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelMemberCode (M := M)) memberCodeGraph := .mk (by
 intro v
 rw [Matrix.fun_eq_vec_three v]
 exact memberCodeGraph_eval _ _ _)

lemma memberFormula_defined : 𝚺ᴬ₁.DefinedRel (modelMember (M := M)) memberFormula := .mk (by
 intro v
 rw [Matrix.fun_eq_vec_two v]
 exact memberFormula_eval _ _)

instance modelMember_definable : 𝚺ᴬ₁-Relation (modelMember (M := M)) :=
 memberFormula_defined.to_definable

end ZFR.ArithmeticRepresentation
