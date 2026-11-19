module
public import UniformGraphSyntax
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M]
lemma unaryCompositionGraph_eval (φ ψ : 𝚺ᴬ₁.Semisentence 2) (y x : M) :
 (compositionGraph φ (fun _ : Fin 1 => ψ)).val.Evalb ![y,x] ↔
 ∃z : M, φ.val.Evalb ![y,z] ∧ ψ.val.Evalb ![z,x] := by
 rw [compositionGraph_eval]
 constructor
 · rintro ⟨w,hy,hw⟩
   have hv : w=![w 0] := by funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
   exact ⟨w 0,by rw [hv] at hy; exact hy,hw 0⟩
 · rintro ⟨z,hy,hz⟩
   refine ⟨![z],hy,?_⟩
   intro i; have hi : i=0 := Subsingleton.elim _ _; subst i; exact hz
end ZFR.ArithmeticRepresentation
