module
public import ExactContextWfNat
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma sourceContextWfFormula_defined : 𝚺ᴬ₁.DefinedPred (modelSourceContextWf (M := M)) sourceContextWfFormula := .mk (by
 intro v
 have hv : v=![v 0] := by funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 rw [hv]
 exact sourceContextWfFormula_eval _)

instance modelSourceContextWf_definable : 𝚺ᴬ₁-Predicate (modelSourceContextWf (M := M)) :=
 sourceContextWfFormula_defined.to_definable

end ZFR.ArithmeticRepresentation
