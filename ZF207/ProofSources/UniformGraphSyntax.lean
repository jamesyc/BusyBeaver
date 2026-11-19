module
public import GraphPrimitiveRecursion
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

/-- Move a graph's bound arguments to free variables to assemble composition. -/
def freeGraph {n} (φ : 𝚺ᴬ₁.Semisentence (n+1)) : ArithmeticFormula (Fin (n+1)) :=
 Rew.bind (L := ℒₒᵣ) (&·) Empty.elim ▹ φ.val

lemma freeGraph_sigma {n} (φ : 𝚺ᴬ₁.Semisentence (n+1)) :
 ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (freeGraph φ) := φ.sigma_prop.rew _

def compositionFree {m n} (φ : 𝚺ᴬ₁.Semisentence (n+1))
 (ψ : Fin n → 𝚺ᴬ₁.Semisentence (m+1)) : ArithmeticFormula (Fin (m+1)) :=
 exsClosure ((Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (n+1)) ![] (&0 :> (#·)) ▹ freeGraph φ) ⋏
  Matrix.conj (fun i => Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (m+1)) ![]
   (#i :> (&·.succ)) ▹ freeGraph (ψ i)))

def compositionGraph {m n} (φ : 𝚺ᴬ₁.Semisentence (n+1))
 (ψ : Fin n → 𝚺ᴬ₁.Semisentence (m+1)) : 𝚺ᴬ₁.Semisentence (m+1) :=
 .mkSigma (Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (m+1)) ![] (#·) ▹ compositionFree φ ψ) (by
  apply Bounding.Hierarchy.rew
  apply Bounding.Hierarchy.exsClosure
  simp [compositionFree,freeGraph_sigma])

variable {M : Type*} [ORingStructure M]

lemma compositionGraph_eval {m n} (φ : 𝚺ᴬ₁.Semisentence (n+1))
 (ψ : Fin n → 𝚺ᴬ₁.Semisentence (m+1)) (y : M) (v : Fin m → M) :
 (compositionGraph φ ψ).val.Evalb (y :> v) ↔
 ∃ w : Fin n → M, φ.val.Evalb (y :> w) ∧ ∀ i, (ψ i).val.Evalb (w i :> v) := by
 simp [compositionGraph,compositionFree,freeGraph,Semiformula.eval_rew,
   Matrix.empty_eq,Empty.eq_elim,Function.comp_def,Matrix.comp_vecCons']

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem compositionGraph_total {m n} (φ : 𝚺ᴬ₁.Semisentence (n+1))
 (ψ : Fin n → 𝚺ᴬ₁.Semisentence (m+1))
 (hφ : GraphTotalIn (M := M) φ) (hψ : ∀ i, GraphTotalIn (M := M) (ψ i)) :
 GraphTotalIn (M := M) (compositionGraph φ ψ) := by
 intro v
 choose w hw hwu using fun i => hψ i v
 obtain ⟨y,hy,hyu⟩ := hφ w
 refine ⟨y,(compositionGraph_eval φ ψ y v).mpr ⟨w,hy,hw⟩,?_⟩
 intro z hz
 obtain ⟨w',hz,hw'⟩ := (compositionGraph_eval φ ψ z v).mp hz
 have he : w'=w := funext (fun i => hwu i (w' i) (hw' i))
 subst w'
 exact hyu z hz
end ZFR.ArithmeticRepresentation
