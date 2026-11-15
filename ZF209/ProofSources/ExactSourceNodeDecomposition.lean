module
public import ExactSourceNodeGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma radix8_exists (n : M) : ∃q t : M,t<8 ∧ n=8*q+t := by
 induction n using ISigma1.sigma1_succ_induction
 · definability
 case zero => exact ⟨0,0,by change (0:M)<(7:M)+1; exact lt_of_le_of_lt (by simp) (lt_add_one (7:M)),by simp⟩
 case succ n ih =>
  obtain ⟨q,t,ht,hn⟩ := ih
  have hle : t+1≤8 := succ_le_iff_lt.mpr ht
  rcases lt_or_eq_of_le hle with hlt|he
  · refine ⟨q,t+1,hlt,?_⟩
    rw [hn,add_assoc]
  · refine ⟨q+1,0,by change (0:M)<(7:M)+1; exact lt_of_le_of_lt (by simp) (lt_add_one (7:M)),?_⟩
    rw [hn,add_assoc,he,mul_add,mul_one,add_zero]

lemma modelSourceNode_surjective (n : M) :
 ∃t a b : M,t<8 ∧ n=modelSourceNode t a b := by
 obtain ⟨q,t,ht,hn⟩ := radix8_exists n
 obtain ⟨a,b,hp⟩ := modelCantor_surjective q
 exact ⟨t,a,b,ht,by rw [modelSourceNode,hp];exact hn⟩

end ZFR.ArithmeticRepresentation
