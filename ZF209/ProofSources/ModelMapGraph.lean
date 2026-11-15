module
public import ModelListMap
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.ModelOperationalConcat
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def mapReverseGraph (φ:𝚺ᴬ₁.Semisentence 3) : 𝚺ᴬ₁.Semisentence 4 :=
 (mapStepsGraph φ).rew (Rew.bind (L:=ℒₒᵣ) ![#0,#1,#1,#2,#3] Empty.elim)
lemma mapReverse_defined (φ:𝚺ᴬ₁.Semisentence 3) (f:M→M→M)
 (hf:𝚺ᴬ₁.DefinedFunction₂ f φ) : 𝚺ᴬ₁.DefinedFunction₃ (mapReverse φ f hf) (mapReverseGraph φ) := .mk (by
 intro v
 simp [mapReverseGraph,mapReverse,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,(mapSteps_defined φ f hf).iff])
def mapGraphOf (mr:𝚺ᴬ₁.Semisentence 4) (rev:𝚺ᴬ₁.Semisentence 3) : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z n t. ∃r, !mr r n 0 t ∧ !rev z r 0”
def mapGraph (φ:𝚺ᴬ₁.Semisentence 3) : 𝚺ᴬ₁.Semisentence 3 :=
 mapGraphOf (mapReverseGraph φ) reverseOntoGraph
lemma mapGraphOf_eval (mr:𝚺ᴬ₁.Semisentence 4) (rev:𝚺ᴬ₁.Semisentence 3)
 (r:M→M→M→M) (v:M→M→M) (hr:𝚺ᴬ₁.DefinedFunction₃ r mr)
 (hv:𝚺ᴬ₁.DefinedFunction₂ v rev) (xs:Fin 3→M) :
 (mapGraphOf mr rev).val.Evalb xs ↔ xs 0=v (r (xs 1) 0 (xs 2)) 0 := by
 simp [mapGraphOf,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,hr.iff,hv.iff]
lemma map_defined (φ:𝚺ᴬ₁.Semisentence 3) (f:M→M→M)
 (hf:𝚺ᴬ₁.DefinedFunction₂ f φ) : 𝚺ᴬ₁.DefinedFunction₂ (map φ f hf) (mapGraph φ) := .mk (by
 intro v
 exact mapGraphOf_eval _ _ _ _ (mapReverse_defined φ f hf) reverseOnto_defined v)
end ZF209.ModelOperationalConcat
