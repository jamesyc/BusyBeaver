import PA215PA.ActualSchedulerBridge
import PA215.Source.SeedScheduler
import PA213.NonhaltingFromSource
import PA213.StateBound

namespace PA213.PA
open PA215.Source

/-- The exact full candidate startup file projects to the independently proved
original intermediate source store. No old binary startup trace is needed. -/
theorem startup_source_eq :
    (⟨.at 68, readFile PA213.Startup.startupFile⟩ : Configuration) =
      SeedPrefix.intermediate := by
  apply congrArg (Configuration.mk (.at 68))
  funext r
  exact (by decide : ∀ r : Fin 9,
    readFile PA213.Startup.startupFile r = SeedPrefix.intermediate.registers r) r

/-- Ordinary PA consistency implies blank-tape nonhalting of the frozen
213-state binary candidate. No source/runtime/coverage supplier is a premise. -/
theorem consistent_machine_nonhalting (hcons : PA215.PA.Consistent) :
    ¬ PA215.Zip.Halts PA213.CandidateTable.machine PA213.Startup.blank := by
  apply PA213.NonhaltingFromSource.blank_nonhalting
  rw [startup_source_eq]
  exact intermediate_nonhalting (PA215.PA.ActualSchedulerBridge.consistent_arithmeticSafe hcons)

#print axioms consistent_machine_nonhalting
end PA213.PA
