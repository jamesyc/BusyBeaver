module
public import ExactSourceShiftEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma sourceShiftGraph_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelSourceShift (M := M)) sourceShiftGraph := .mk (by
 intro v
 have hv : v=![v 0,v 1,v 2] := by
  funext i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  exact Fin.cases rfl (fun x => Fin.elim0 x) i
 rw [hv]
 exact sourceShiftGraph_eval _ _ _)

end ZFR.ArithmeticRepresentation
