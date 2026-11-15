module
public import ExactSourceNodeGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma modelCantor_sum_le_double (a b : M) : 2*(a+b)≤2*modelCantor a b := by
 by_cases hs : a+b=0
 · rw [hs]; simp
 · have hp : 0<a+b := pos_iff_ne_zero.mpr hs
   have h1 : 1≤a+b := one_le_of_zero_lt _ hp
   have h2 : 2≤(a+b)+1 := by
     simpa only [one_add_one_eq_two] using (_root_.add_le_add h1 (_root_.le_refl (1:M)))
   calc
    2*(a+b) ≤ ((a+b)+1)*(a+b) := mul_le_mul_of_nonneg_right h2 (by simp)
    _ = (a+b)*((a+b)+1) := mul_comm _ _
    _ ≤ (a+b)*((a+b)+1)+2*b := by simp
    _ = 2*modelCantor a b := (modelCantor_equation a b).symm

lemma modelCantor_sum_le (a b : M) : a+b≤modelCantor a b := by
 by_contra hn
 have hlt : modelCantor a b<a+b := _root_.lt_of_not_ge hn
 have hh := mul_lt_mul_of_pos_left hlt (by simp : (0:M)<2)
 exact (_root_.not_lt_of_ge (modelCantor_sum_le_double a b)) hh

lemma modelCantor_left_le (a b : M) : a≤modelCantor a b :=
 le_trans (by simp : a≤a+b) (modelCantor_sum_le a b)
lemma modelCantor_right_le (a b : M) : b≤modelCantor a b :=
 le_trans (by simp : b≤a+b) (modelCantor_sum_le a b)

lemma model_one_lt_eight : (1:M)<8 := by
 have h : (1:M)≤7 := by
   have hh := add_le_add_right (show (0:M)≤6 by simp) (1:M)
   change (1:M)≤(6:M)+1
   simpa only [add_zero,zero_add,add_comm] using hh
 exact lt_of_le_of_lt h (lt_add_one (7:M))

lemma modelSourceNode_payload_lt (t a b : M) (hn : 0<modelSourceNode t a b) :
 modelCantor a b<modelSourceNode t a b := by
 by_cases hq : modelCantor a b=0
 · rw [hq]; exact hn
 · have hp : 0<modelCantor a b := pos_iff_ne_zero.mpr hq
   have hh := mul_lt_mul_of_pos_right (model_one_lt_eight (M := M)) hp
   have hh' : modelCantor a b<8*modelCantor a b := by simpa only [one_mul] using hh
   exact lt_of_lt_of_le hh' (by simp [modelSourceNode])

lemma modelSourceNode_left_lt (t a b : M) (hn : 0<modelSourceNode t a b) :
 a<modelSourceNode t a b := lt_of_le_of_lt (modelCantor_left_le a b) (modelSourceNode_payload_lt t a b hn)
lemma modelSourceNode_right_lt (t a b : M) (hn : 0<modelSourceNode t a b) :
 b<modelSourceNode t a b := lt_of_le_of_lt (modelCantor_right_le a b) (modelSourceNode_payload_lt t a b hn)


end ZFR.ArithmeticRepresentation
