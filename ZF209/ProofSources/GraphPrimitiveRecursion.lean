module
public import ModelPrimitiveRecursion
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Unique-output totality for an explicit arithmetic graph in a model. -/
def GraphTotalIn {n} (φ : 𝚺ᴬ₁.Semisentence (n+1)) : Prop :=
 ∀ v : Fin n → M, ∃! z : M, φ.val.Evalb (z :> v)

noncomputable def graphValue {n} (φ : 𝚺ᴬ₁.Semisentence (n+1))
 (h : GraphTotalIn (M := M) φ) (v : Fin n → M) : M := Classical.choose! (h v)

lemma graphValue_spec {n} (φ : 𝚺ᴬ₁.Semisentence (n+1))
 (h : GraphTotalIn (M := M) φ) (z : M) (v : Fin n → M) :
 φ.val.Evalb (z :> v) ↔ z=graphValue φ h v := by
 simp only [graphValue,Classical.choose!_eq_iff_right]

end ZFR.ArithmeticRepresentation
