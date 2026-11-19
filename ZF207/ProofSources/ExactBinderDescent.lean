module
public import ExactSourceDescent
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma modelSourceNode_left_succ_lt (t a b : M) (ht : 1<t) :
 a+1<modelSourceNode t a b := by
 have hp : modelCantor a b≤8*modelCantor a b := by
   simpa only [one_mul] using (mul_le_mul_of_nonneg_right
     (le_of_lt (model_one_lt_eight (M := M))) (show 0≤modelCantor a b by simp))
 have ha : a≤8*modelCantor a b := le_trans (modelCantor_left_le a b) hp
 have hle : a+1≤8*modelCantor a b+1 := _root_.add_le_add ha (_root_.le_refl _)
 have hlt : 8*modelCantor a b+1<8*modelCantor a b+t := by
   simpa only [add_comm] using (_root_.add_lt_add_left ht (8*modelCantor a b))
 exact lt_of_le_of_lt hle hlt

lemma modelBinderIndex_descent (d t a : M) (ht : 1<t) :
 modelCantor (d+1) a<modelCantor d (modelSourceNode t a 0) := by
 apply modelCantor_sum_lt
 have h := _root_.add_lt_add_left (modelSourceNode_left_succ_lt t a 0 ht) d
 simpa only [add_assoc,add_comm,add_left_comm] using h

end ZFR.ArithmeticRepresentation
