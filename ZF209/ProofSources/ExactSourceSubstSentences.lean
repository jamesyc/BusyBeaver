module
public import ExactSourceSubstEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma sourceSubstGraph_defined : 𝚺ᴬ₁.DefinedFunction₃ (modelSourceSubst (M := M)) sourceSubstGraph := .mk (by
 intro v
 have hv : v=![v 0,v 1,v 2,v 3] := by
  funext i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  exact Fin.cases rfl (fun x => Fin.elim0 x) i
 rw [hv]
 exact sourceSubstGraph_eval _ _ _ _)

end ZFR.ArithmeticRepresentation
