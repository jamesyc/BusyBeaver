import User211SourceEquivalence
import PA215.Source.PhysicalRegisters
import PA213.StartupData
import PA215PA.ActualSchedulerBridge
import PA215.Source.SeedScheduler
namespace PA211.UserCandidate.Source
open PA215.Source

/-- Ordinary PA consistency, not consistency of Lean, gives nonhalting of the
unchanged source interpreter at the actual startup intermediate. The new
binary table must still be joined to this source by its own runtime proof. -/
theorem consistent_source_nonhalting (hcons : PA215.PA.Consistent) :
    ¬ CycleHalts sites SeedPrefix.intermediate := by
  intro hh
  exact intermediate_nonhalting
    (PA215.PA.ActualSchedulerBridge.consistent_arithmeticSafe hcons)
    ((cycleHalts_iff _).mp hh)
theorem startup_source_eq :
    (⟨.at 68,readFile PA213.Startup.startupFile⟩ : Configuration)=SeedPrefix.intermediate := by
  apply congrArg (Configuration.mk (.at 68))
  funext r
  exact (by decide : ∀ r : Fin 9, readFile PA213.Startup.startupFile r=SeedPrefix.intermediate.registers r) r

theorem consistent_baseline_startup_nonhalting (hcons : PA215.PA.Consistent) :
    ¬ CycleHalts exactSites ⟨.at 68,readFile PA213.Startup.startupFile⟩ := by
  rw [startup_source_eq]
  exact intermediate_nonhalting (PA215.PA.ActualSchedulerBridge.consistent_arithmeticSafe hcons)

#print axioms consistent_source_nonhalting
#print axioms startup_source_eq
#print axioms consistent_baseline_startup_nonhalting
end PA211.UserCandidate.Source
