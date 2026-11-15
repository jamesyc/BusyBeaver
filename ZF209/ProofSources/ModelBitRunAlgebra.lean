module
public import ModelBitRuns
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Genuine internal addition of run lengths in any PA model. -/
lemma bitRun_add (n m b tail:M) :
 bitRun (n+m) b tail=bitRun n b (bitRun m b tail) := by
 induction n using ISigma1.sigma1_succ_induction
 · definability
 case zero => simp only [zero_add,bitRun_zero]
 case succ n ih =>
  have ha:(n+1)+m=(n+m)+1 := by ac_rfl
  rw [ha,bitRun_succ,bitRun_succ,ih]
end ZF209.BinaryTape
