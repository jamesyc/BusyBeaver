import User211EndpointInternalStartupHaltingBridge
import User211InternalActualRefutationSentences
import PA213PA.InternalActualRefutationHalting
namespace PA211.UserCandidate.PA.InternalActualRefutation
open PA215 PA215.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- Reuses only the original uniform coded-source refutation compiler, not its
old physical machine. The fresh all-model runtime supplies the new blank halt. -/
theorem refutation_implies_blank (code : V) (hc : ActualCheckerBlueprint.verifyValue code=2) :
    V ⊧/![] HaltingFormula.traceSentence := by
  obtain ⟨n,cs,d,ht,hd⟩ := PA213.PA.InternalActualRefutation.refutation_seed_halts code hc
  obtain ⟨k,ds,e,he,hz⟩ :=
    PA213.PA.InternalTrace.FixedTrace.seed_halts_iff_intermediate.mp ⟨n,cs,d,ht,hd⟩
  exact InternalTrace.FixedTrace.intermediate_halt_implies_blank he hz
/-- Actual ordinary PA proof, with no runtime, scheduler or source premise. -/
theorem pa_proves_refutation_halting : theory ⊢ refutationHaltingSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  rw [models_iff,refutationHalting_correct]
  exact refutation_implies_blank
theorem pa_proves_nonhalting_no_actual_refutation : theory ⊢ nonhaltingNoActualRefutationSentence :=
  pa_proves_runtime_contraposition ⨀ pa_proves_refutation_halting
#print axioms refutation_implies_blank
#print axioms pa_proves_refutation_halting
#print axioms pa_proves_nonhalting_no_actual_refutation
end PA211.UserCandidate.PA.InternalActualRefutation
