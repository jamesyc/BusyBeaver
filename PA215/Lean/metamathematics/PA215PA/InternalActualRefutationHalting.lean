import PA215PA.InternalActualRefutationSentences
import PA215PA.InternalCodedSourceSeedRoot
import PA215PA.InternalCodedSourceEnumeration
import PA215PA.InternalSeedHaltingBridge
namespace PA215.PA.InternalActualRefutation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open InternalTrace InternalTrace.CodedSource
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- Uniform literal source execution, beginning at the exact existing seed. -/
theorem refutation_seed_halts (code : V) (hc : ActualCheckerBlueprint.verifyValue code=2) :
    ∃ k cs d : V,Trace k cs FixedTrace.seedState d ∧ control d=0 := by
  obtain ⟨n,cs,xs,hn,ht,hv,hclean,hN,hL⟩ := seed_to_root (V:=V)
  obtain ⟨m,ds,d,hu,hhalt⟩ := refutation_root_halts code xs hv hclean hN hL hc
  obtain ⟨es,he⟩ := trace_compose ht hu
  exact ⟨n+m,es,d,he,hhalt⟩

/-- Accepted V1 actual-basis refutations imply the original exact blank-halting
sentence, uniformly in every PA model. -/
theorem refutation_implies_blank (code : V) (hc : ActualCheckerBlueprint.verifyValue code=2) :
    V ⊧/![] HaltingFormula.traceSentence := by
  obtain ⟨n,cs,d,ht,hd⟩ := refutation_seed_halts code hc
  exact FixedTrace.seed_halt_implies_blank ht hd

/-- Actual ordinary PA proof; no source, runtime, oracle or scheduler premise. -/
theorem pa_proves_refutation_halting : theory ⊢ refutationHaltingSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  rw [models_iff,refutationHalting_correct]
  exact refutation_implies_blank

/-- PA proves that nonhalting excludes an actual-basis refutation code. InternalActualRefutationConsistency relates this sentence to PA consistency. -/
theorem pa_proves_nonhalting_no_actual_refutation : theory ⊢ nonhaltingNoActualRefutationSentence :=
  pa_proves_runtime_contraposition ⨀ pa_proves_refutation_halting
#print axioms refutation_seed_halts
#print axioms refutation_implies_blank
#print axioms pa_proves_refutation_halting
#print axioms pa_proves_nonhalting_no_actual_refutation
end PA215.PA.InternalActualRefutation
