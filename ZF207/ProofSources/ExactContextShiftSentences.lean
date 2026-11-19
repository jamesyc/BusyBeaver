module
public import ExactContextShiftNat
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma sourceContextShiftGraph_defined : 𝚺ᴬ₁.DefinedFunction₁ (modelSourceContextShift (M := M)) sourceContextShiftGraph := .mk (by
 intro v
 have hv : v=![v 0,v 1] := by funext i; refine Fin.cases rfl (fun i => ?_) i; exact Fin.cases rfl (fun x => Fin.elim0 x) i
 rw [hv]
 exact sourceContextShiftGraph_eval _ _)

instance modelSourceContextShift_definable : 𝚺ᴬ₁-Function₁ (modelSourceContextShift (M := M)) :=
 sourceContextShiftGraph_defined.to_definable

end ZFR.ArithmeticRepresentation
