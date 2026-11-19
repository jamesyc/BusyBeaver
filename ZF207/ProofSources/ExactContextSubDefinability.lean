module
public import ExactContextSubNat
public import ExactContextSubPredicate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma contextSubCodeGraph_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelContextSubCode (M := M)) contextSubCodeGraph := .mk (by
 intro v
 have hv : v=![v 0,v 1,v 2] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]
 exact contextSubCodeGraph_eval _ _ _)

lemma contextSubFormula_defined : 𝚺ᴬ₁.DefinedRel (modelContextSub (M := M)) contextSubFormula := .mk (by
 intro v
 have hv : v=![v 0,v 1] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]
 exact contextSubFormula_eval _ _)

instance modelContextSub_definable : 𝚺ᴬ₁-Relation (modelContextSub (M := M)) :=
 contextSubFormula_defined.to_definable

end ZFR.ArithmeticRepresentation
