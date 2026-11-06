import PA215PA.Startup.SourceBinding
import PA215.Source.SeedPrefix

namespace PA215.PA.Startup

theorem intermediate_matches_sourceEntry : Source.SeedPrefix.intermediate = sourceEntry := by
  unfold Source.SeedPrefix.intermediate sourceEntry
  congr 1
  funext r
  exact (by decide : ∀ r : Fin 9,
    (if r = 2 then 6 else if r = 7 then 7 else 0) = entryRegisters r) r

/-- Actual source steps connect the clean virtual seed to the source state
bound to the complete physical startup frame. -/
theorem seed_to_startup_source :
    Source.Steps Source.exactSites 159 Source.SeedPrefix.seed sourceEntry := by
  rw [← intermediate_matches_sourceEntry]
  exact Source.SeedPrefix.trace

theorem seed_halts_iff_startup_source :
    Source.CycleHalts Source.exactSites Source.SeedPrefix.seed ↔
      Source.CycleHalts Source.exactSites sourceEntry := by
  rw [← intermediate_matches_sourceEntry]
  exact Source.SeedPrefix.halting_iff

#print axioms intermediate_matches_sourceEntry
#print axioms seed_to_startup_source
#print axioms seed_halts_iff_startup_source
end PA215.PA.Startup
