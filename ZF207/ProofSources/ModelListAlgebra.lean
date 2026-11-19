module
public import ModelListInduction
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelOperationalConcat
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma append_nil (n:M) : append n 0=n := by
 induction n using ISigma1.sigma1_order_induction
 · definability
 case ind n ih =>
  by_cases hn:n=0
  · subst n; exact append_zero 0
  · have hp:=pos_iff_ne_zero.mpr hn
    have hh:=ih _ (modelListTail_lt n hp)
    nth_rw 1 [←modelList_reconstruct n hp]
    rw [append_cons,hh,modelList_reconstruct n hp]
lemma append_assoc (n:M) : ∀b c:M,append (append n b) c=append n (append b c) := by
 induction n using ISigma1.pi1_order_induction
 · definability
 case ind n ih =>
  by_cases hn:n=0
  · subst n; intro b c; simp only [append_zero]
  · have hp:=pos_iff_ne_zero.mpr hn
    have hh:=ih _ (modelListTail_lt n hp)
    intro b c
    rw [←modelList_reconstruct n hp]
    simp only [append_cons,hh]
lemma reverseOnto_append (n:M) : ∀b c:M,
 reverseOnto (append n b) c=reverseOnto b (reverseOnto n c) := by
 induction n using ISigma1.pi1_order_induction
 · definability
 case ind n ih =>
  by_cases hn:n=0
  · subst n; intro b c; simp only [append_zero,reverseOnto_zero]
  · have hp:=pos_iff_ne_zero.mpr hn
    have hh:=ih _ (modelListTail_lt n hp)
    intro b c
    rw [←modelList_reconstruct n hp]
    simp only [append_cons,reverseOnto_cons,hh]
end ZF207.ModelOperationalConcat
