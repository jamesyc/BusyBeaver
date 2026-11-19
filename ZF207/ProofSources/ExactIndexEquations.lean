module
public import GraphPrimitiveRecursion
public import NumericTransform
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def shiftIndexGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “y d i. (i < d ∧ y = i) ∨ (i ≮ d ∧ y = i + 1)”
def substIndexGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
 “y d t i. (i < d ∧ y = i) ∨ (i = d ∧ y = t + d) ∨ (d < i ∧ y + 1 = i)”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma shiftIndexGraph_total : GraphTotalIn (M := M) shiftIndexGraph := by
 classical
 intro v
 by_cases h : v 1 < v 0
 · refine ⟨v 1,?_,?_⟩ <;> simp [shiftIndexGraph,h]
 · refine ⟨v 1+1,?_,?_⟩ <;> simp [shiftIndexGraph,h]

lemma substIndexGraph_total : GraphTotalIn (M := M) substIndexGraph := by
 intro v
 rcases lt_trichotomy (v 2) (v 0) with h|h|h
 · refine ⟨v 2,?_,?_⟩ <;> simp [substIndexGraph,h,ne_of_lt h,not_lt_of_gt h]
 · refine ⟨v 1+v 0,?_,?_⟩ <;> simp [substIndexGraph,h]
 · have hi : 0<v 2 := lt_of_le_of_lt (by simp) h
   obtain ⟨j,hj⟩ := eq_succ_of_pos hi
   refine ⟨j,?_,?_⟩
   · have hh : (v 2<v 0 ∧ j=v 2) ∨ (v 2=v 0 ∧ j=v 1+v 0) ∨ (v 0<v 2 ∧ j+1=v 2) :=
       Or.inr (Or.inr ⟨h,hj.symm⟩)
     simpa [substIndexGraph] using hh
   · intro y hy
     have he : y+1=v 2 := by simpa [substIndexGraph,h,not_lt_of_gt h,ne_of_gt h] using hy
     exact add_right_cancel (he.trans hj)

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem shiftIndexGraph_exact (y d i : Nat) :
 shiftIndexGraph.val.Evalb ![y,d,i] ↔ y=sourceShiftIndex d i := by
 by_cases h : i<d <;> simp [shiftIndexGraph,sourceShiftIndex,h]

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem substIndexGraph_exact (y d t i : Nat) :
 substIndexGraph.val.Evalb ![y,d,t,i] ↔ y=sourceSubstIndex t d i := by
 by_cases h : i<d
 · simp [substIndexGraph,sourceSubstIndex,h,show i≠d by omega,show ¬d<i by omega]
 · by_cases he : i=d
   · simp [substIndexGraph,sourceSubstIndex,h,he]
   · simp [substIndexGraph,sourceSubstIndex,h,he,show d<i by omega]
     omega

end ZFR.ArithmeticRepresentation
