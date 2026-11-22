module
public import ZF192Support.Coding.Histories.TraceFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
instance modelTailIter_definable : 𝚺ᴬ₁-Function₂ (modelTailIter (M:=M)) := tailIterationGraph_defined.to_definable
instance modelListTail_definable : 𝚺ᴬ₁-Function₁ (modelListTail (M:=M)) := ruleTail_defined.to_definable
lemma modelListTail_zero : modelListTail (0:M)=0 := by
 have hp : modelPredecessor (0:M)=0 := by
  symm
  apply (predecessorGraph_value _ _).mp
  exact (predecessorGraph_eval _ _).mpr (Or.inl ⟨rfl,rfl⟩)
 rw [modelListTail,hp,←modelCantor_zero,modelUnpairRight_pair]
 exact modelCantor_zero.symm

lemma modelTailIter_at_zero (k : M) : modelTailIter k (0:M)=0 := by
 induction k using ISigma1.sigma1_succ_induction
 · definability
 case zero => exact modelTailIter_zero 0
 case succ k ih => rw [modelTailIter_succ,ih,modelListTail_zero]
lemma modelTailIter_commute (k n : M) : modelTailIter k (modelListTail n)=modelTailIter (k+1) n := by
 induction k using ISigma1.sigma1_succ_induction
 · definability
 case zero => rw [modelTailIter_zero,modelTailIter_succ,modelTailIter_zero]
 case succ k ih => rw [modelTailIter_succ,ih,modelTailIter_succ (k+1)]
lemma modelTailIter_stops (k n : M) (hn:n≤k) : modelTailIter k n=0 := by
 have hh : ∀k : M, ∀n≤k, modelTailIter k n=0 := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
   intro n hn
   have hz:n=0 := le_antisymm hn (by simp)
   rw [hz,modelTailIter_zero]
  case succ k ih =>
   intro n hn
   by_cases hz:n=0
   · rw [hz,modelTailIter_at_zero]
   · rw [←modelTailIter_commute]
     apply ih
     have hlt := modelListTail_lt n (pos_iff_ne_zero.mpr hz)
     exact lt_succ_iff_le.mp (lt_of_lt_of_le hlt hn)
 exact hh k n hn
end ZFR.ArithmeticRepresentation
