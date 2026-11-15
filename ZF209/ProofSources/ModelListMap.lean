module
public import ModelMapAccumulator
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.ModelOperationalConcat
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (φ:𝚺ᴬ₁.Semisentence 3) (f:M→M→M) (hf:𝚺ᴬ₁.DefinedFunction₂ f φ)
lemma mapReverse_acc (n:M) : ∀b t:M,
 mapReverse φ f hf n b t=append (mapReverse φ f hf n 0 t) b := by
 haveI : 𝚺ᴬ₁-Function₂ f := hf.to_definable
 induction n using ISigma1.pi1_order_induction
 · definability
 case ind n ih =>
  by_cases hn:n=0
  · subst n; intro b t; simp only [mapReverse_zero,append_zero]
  · have hp:=pos_iff_ne_zero.mpr hn
    have hh:=ih _ (modelListTail_lt n hp)
    intro b t
    rw [←modelList_reconstruct n hp]
    simp only [mapReverse_cons]
    rw [hh (modelListCons (f (modelListHead n) t) b) t,
      hh (modelListCons (f (modelListHead n) t) 0) t,append_assoc,append_cons,append_zero]
noncomputable def map (n t:M) : M := reverseOnto (mapReverse φ f hf n 0 t) 0
instance map_definable : 𝚺ᴬ₁-Function₂ (map φ f hf) := by
 unfold map
 definability
lemma map_zero (t:M) : map φ f hf 0 t=0 := by simp only [map,mapReverse_zero,reverseOnto_zero]
lemma map_cons (a n t:M) : map φ f hf (modelListCons a n) t=modelListCons (f a t) (map φ f hf n t) := by
 change reverseOnto (mapReverse φ f hf (modelListCons a n) 0 t) 0=
  modelListCons (f a t) (reverseOnto (mapReverse φ f hf n 0 t) 0)
 rw [mapReverse_cons,mapReverse_acc,reverseOnto_append,reverseOnto_cons,reverseOnto_zero]
lemma map_ne_zero {n:M} (t:M) (hn:n≠0) : map φ f hf n t≠0 := by
 rw [←modelList_reconstruct n (pos_iff_ne_zero.mpr hn),map_cons]
 exact cons_ne_zero _ _
lemma map_head {n:M} (t:M) (hn:n≠0) :
 modelListHead (map φ f hf n t)=f (modelListHead n) t := by
 rw [←modelList_reconstruct n (pos_iff_ne_zero.mpr hn)]
 simp only [map_cons,modelListHead_cons]
end ZF209.ModelOperationalConcat
