module
public import ExactCantorGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance modelCantor_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelCantor (M := M)) exactCantorGraph := .mk (by
 intro v
 have hv : (v 0 :> ![v 1,v 2])=v := by
   funext i
   refine Fin.cases ?_ (fun j=>?_) i
   · rfl
   · refine Fin.cases ?_ (fun j=>?_) j
     · rfl
     · refine Fin.cases ?_ (fun j=>Fin.elim0 j) j
       rfl
 change exactCantorGraph.val.Evalb v ↔ v 0=modelCantor (v 1) (v 2)
 simpa only [hv,modelCantor] using graphValue_spec exactCantorGraph exactCantorGraph_total (v 0) ![v 1,v 2])
instance modelCantor_definable : 𝚺ᴬ₁.DefinableFunction₂ (modelCantor (M := M)) := modelCantor_defined.to_definable

lemma modelCantor_zero : modelCantor (0:M) 0=0 := by
 symm
 apply modelCantor_unique
 simp

lemma modelCantor_next_diagonal (x b : M) :
 modelCantor x (b+1)=modelCantor (x+1) b+1 := by
 symm
 apply modelCantor_unique
 rw [mul_add,modelCantor_equation]
 simp only [mul_add,add_mul,mul_one,one_mul]
 ac_rfl

lemma modelCantor_next_axis (b : M) : modelCantor (b+1) 0=modelCantor 0 b+1 := by
 symm
 apply modelCantor_unique
 rw [mul_add,modelCantor_equation]
 simp only [zero_add,add_zero,mul_zero,zero_mul,mul_one,one_mul,
   ←one_add_one_eq_two,mul_add,add_mul,mul_one,one_mul]
 ac_rfl

lemma modelCantor_surjective (n : M) : ∃ a b, modelCantor a b=n := by
 induction n using ISigma1.sigma1_succ_induction
 · definability
 case zero => exact ⟨0,0,modelCantor_zero⟩
 case succ n ih =>
   obtain ⟨a,b,h⟩ := ih
   by_cases ha : a=0
   · subst a
     exact ⟨b+1,0,by rw [modelCantor_next_axis,h]⟩
   · obtain ⟨x,hx⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr ha)
     subst a
     exact ⟨x,b+1,by rw [modelCantor_next_diagonal,h]⟩

lemma triangular_next (s : M) :
 (s+1)*((s+1)+1)=s*(s+1)+2*s+2 := by
 simp only [←one_add_one_eq_two,mul_add,add_mul,mul_one,one_mul]
 ac_rfl

lemma modelCantor_sum_lt (a b c d : M) (h : a+b<c+d) :
 modelCantor a b<modelCantor c d := by
 have hb : b≤a+b := by simp
 have hs : a+b+1≤c+d := succ_le_iff_lt.mpr h
 have hp : (a+b+1)*((a+b+1)+1)≤(c+d)*((c+d)+1) :=
   mul_le_mul hs (_root_.add_le_add hs (_root_.le_refl 1)) (by simp) (by simp)
 have hpair : 2*modelCantor a b<2*modelCantor c d := calc
   2*modelCantor a b = (a+b)*((a+b)+1)+2*b := modelCantor_equation a b
   _ ≤ (a+b)*((a+b)+1)+2*(a+b) := _root_.add_le_add (_root_.le_refl _) (mul_le_mul_of_nonneg_left hb (by simp))
   _ < (a+b)*((a+b)+1)+2*(a+b)+2 := by simp
   _ = (a+b+1)*((a+b+1)+1) := (triangular_next (a+b)).symm
   _ ≤ (c+d)*((c+d)+1) := hp
   _ ≤ (c+d)*((c+d)+1)+2*d := by simp
   _ = 2*modelCantor c d := (modelCantor_equation c d).symm
 by_contra hn
 have hle := _root_.not_lt.mp hn
 have hh := mul_le_mul_of_nonneg_left hle (by simp : (0:M)≤2)
 exact (_root_.not_lt_of_ge hh) hpair

lemma modelCantor_injective {a b c d : M} (h : modelCantor a b=modelCantor c d) :
 a=c ∧ b=d := by
 have hs : a+b=c+d := by
   rcases lt_trichotomy (a+b) (c+d) with hl|he|hr
   · have hh := modelCantor_sum_lt a b c d hl
     rw [h] at hh
     exact False.elim (_root_.lt_irrefl _ hh)
   · exact he
   · have hh := modelCantor_sum_lt c d a b hr
     rw [h] at hh
     exact False.elim (_root_.lt_irrefl _ hh)
 have he := congrArg (fun z:M => 2*z) h
 rw [modelCantor_equation,modelCantor_equation,←hs] at he
 have hb : b=d := mul_left_cancel₀ (by simp : (2:M)≠0) (add_left_cancel he)
 subst d
 exact ⟨add_right_cancel hs,rfl⟩

end ZFR.ArithmeticRepresentation
