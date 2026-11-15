module
public import ExactSourceWfNat
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma sourceWfCodeGraph_defined : 𝚺ᴬ₁.DefinedFunction₁ (modelSourceWfCode (M := M)) sourceWfCodeGraph := .mk (by
 intro v
 have hv : v=![v 0,v 1] := by
  funext i; refine Fin.cases rfl (fun i => ?_) i
  exact Fin.cases rfl (fun x => Fin.elim0 x) i
 rw [hv]
 exact sourceWfCodeGraph_eval _ _)

lemma sourceWfFormula_defined : 𝚺ᴬ₁.DefinedPred (modelSourceWf (M := M)) sourceWfFormula := .mk (by
 intro v
 have hv : v=![v 0] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 rw [hv]
 exact sourceWfFormula_eval _)

instance modelSourceWf_definable : 𝚺ᴬ₁-Predicate (modelSourceWf (M := M)) :=
 sourceWfFormula_defined.to_definable

end ZFR.ArithmeticRepresentation
