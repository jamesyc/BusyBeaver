module
public import ModelReverseAccumulator
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelOperationalConcat
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
instance reverseOnto_definable : 𝚺ᴬ₁-Function₂ (reverseOnto (M:=M)) := by
 unfold reverseOnto
 definability
noncomputable def append (n b:M) : M := reverseOnto (reverseOnto n 0) b
instance append_definable : 𝚺ᴬ₁-Function₂ (append (M:=M)) := by
 unfold append
 definability
lemma append_zero (b:M) : append 0 b=b := by simp only [append,reverseOnto_zero]
lemma reverseOnto_reverseOnto (n:M) : ∀ b c:M,
 reverseOnto (reverseOnto n b) c=reverseOnto b (append n c) := by
 induction n using ISigma1.pi1_order_induction
 · definability
 case ind n ih =>
  by_cases hn:n=0
  · subst n; intro b c; simp only [reverseOnto_zero,append_zero]
  · have hp:=pos_iff_ne_zero.mpr hn
    have hrec:=modelList_reconstruct n hp
    have hlt:=modelListTail_lt n hp
    have hh:=ih (modelListTail n) hlt
    intro b c
    nth_rw 1 [←hrec]
    rw [reverseOnto_cons,hh,reverseOnto_cons]
    congr 1
    conv_rhs => rw [←hrec]
    simp only [append,reverseOnto_cons]
    conv_rhs => rw [hh,reverseOnto_cons,reverseOnto_zero]
    rfl
lemma append_cons (a n b:M) : append (modelListCons a n) b=modelListCons a (append n b) := by
 simp only [append,reverseOnto_cons]
 rw [reverseOnto_reverseOnto,reverseOnto_cons,reverseOnto_zero]
 rfl
lemma append_ne_zero_right (n:M) {b:M} (hb:b≠0) : append n b≠0 := by
 by_cases hn:n=0
 · subst n; simpa only [append_zero] using hb
 · rw [←modelList_reconstruct n (pos_iff_ne_zero.mpr hn),append_cons]
   exact cons_ne_zero _ _
lemma append_head_eq (n b c:M) (h:modelListHead b=modelListHead c) :
 modelListHead (append n b)=modelListHead (append n c) := by
 by_cases hn:n=0
 · subst n; simpa only [append_zero] using h
 · rw [←modelList_reconstruct n (pos_iff_ne_zero.mpr hn)]
   simp only [append_cons,modelListHead_cons]

end ZF207.ModelOperationalConcat
