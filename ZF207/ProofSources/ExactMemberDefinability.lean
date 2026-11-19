module
public import ExactMemberNat
public import ExactMemberPredicate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma memberCodeGraph_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelMemberCode (M := M)) memberCodeGraph := .mk (by
 intro v
 have hv : v=![v 0,v 1,v 2] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]
 exact memberCodeGraph_eval _ _ _)

lemma memberFormula_defined : 𝚺ᴬ₁.DefinedRel (modelMember (M := M)) memberFormula := .mk (by
 intro v
 have hv : v=![v 0,v 1] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]
 exact memberFormula_eval _ _)

instance modelMember_definable : 𝚺ᴬ₁-Relation (modelMember (M := M)) :=
 memberFormula_defined.to_definable

end ZFR.ArithmeticRepresentation
