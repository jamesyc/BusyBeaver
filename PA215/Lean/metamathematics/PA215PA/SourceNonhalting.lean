import PA215PA.ActualSchedulerBridge
import PA215PA.Startup.SeedBinding
import PA215.Source.SeedScheduler

/-! Consistency of PA implies nonhalting of the literal cyclic source under its AX semantics. MachineNonhaltingV2 transports the result to the blank physical machine. -/
namespace PA215.PA

/-- The clean virtual seed follows the actual initial AX command into the
proved arithmetic schedule. -/
theorem consistent_seed_nonhalting (hcons : Consistent) :
    ¬ Source.CycleHalts Source.exactSites Source.SeedPrefix.seed :=
  Source.seed_nonhalting (ActualSchedulerBridge.consistent_arithmeticSafe hcons)

/-- The exact intermediate AX source state reached by physical startup. -/
theorem consistent_intermediate_nonhalting (hcons : Consistent) :
    ¬ Source.CycleHalts Source.exactSites Source.SeedPrefix.intermediate :=
  Source.intermediate_nonhalting (ActualSchedulerBridge.consistent_arithmeticSafe hcons)

/-- The same source configuration with its exact startup file projection. -/
theorem consistent_startup_source_nonhalting (hcons : Consistent) :
    ¬ Source.CycleHalts Source.exactSites Startup.sourceEntry := by
  rw [← Startup.intermediate_matches_sourceEntry]
  exact consistent_intermediate_nonhalting hcons

#print axioms consistent_seed_nonhalting
#print axioms consistent_intermediate_nonhalting
#print axioms consistent_startup_source_nonhalting
end PA215.PA
