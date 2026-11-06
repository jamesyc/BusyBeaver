import PA215PA.SourceNonhalting
import PA215PA.TraceAdequacy
import PA215.Source.CachedV2.SourceToPhysical
import PA215.Source.AllContractDestinations
import PA215.AllRuntimeCertificates

/-! If ordinary PA is consistent, the 215-state machine runs forever on the blank
tape. The startup equivalence connects the physical machine to the exact source
program. The runtime certificates and destination checks supply the simulation
for each source instruction. NonhaltingUnprovability gives the separate
object-theoretic result for the same arithmetic nonhalting sentence. -/
namespace PA215.PA.CachedV2
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- The literal transition table on a blank tape, with 215 working states. -/
theorem consistent_machine_nonhalting (hcons : Consistent) :
    ¬ PA215.Halts PA215.blank := by
  have hs : ¬ Source.CycleHalts Source.exactSites
      ⟨.at 68, Source.readFile Startup.startupFile⟩ := by
    rw [← Startup.sourceEntry_matches_file]
    exact consistent_startup_source_nonhalting hcons
  have hv : 10 ≤ Startup.startupFile.length := by
    rw [Startup.full_file_length]
    decide
  have hn := Source.CachedV2.source_nonhalt_to_physical
    AllRuntimeCertificates.nonterminalCoverage Source.original_all_destinations_agree
    Startup.source_site68 hv hs 0
  intro hh
  exact hn (Startup.blank_halts_iff_native_frame.mp hh)

/-- Standard-model truth of the already fixed arithmetic nonhalting sentence.
No object-level PA derivation of this sentence is asserted. -/
theorem consistent_nonhalting_sentence (hcons : Consistent) :
    Nat ⊧/![] HaltingFormula.nonhaltingSentence :=
  HaltingFormula.nonhaltingSentence_iff.mpr (consistent_machine_nonhalting hcons)

#print axioms consistent_machine_nonhalting
#print axioms consistent_nonhalting_sentence
end PA215.PA.CachedV2
