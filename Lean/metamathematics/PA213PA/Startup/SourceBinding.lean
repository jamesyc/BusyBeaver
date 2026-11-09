module

public import PA215.Source.PhysicalRegisters
public import PA213PA.Startup.Data
public import PA215.Source.ExactSource

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA213.PA.Startup
open PA215

/-- This is the intermediate AX store, not the clean paper AX25 entry. -/
def entryRegisters : Source.Registers := fun r =>
  ([0,0,6,0,0,0,0,7,0] : List Nat).getD r.val 0

theorem logical_projection : Source.readFile startupFile = entryRegisters := by
  funext r
  exact (by decide : ∀ r : Fin 9, Source.readFile startupFile r = entryRegisters r) r

/-- Literal source binding: the saved path is ordinal68, immediately before IncW. -/
theorem source_site68 :
    Source.exactSites[68]? = some ⟨startupPath, .inc 2⟩ := by decide

def sourceEntry : Source.Configuration := ⟨.at 68, entryRegisters⟩

theorem sourceEntry_matches_file :
    sourceEntry = ⟨.at 68, Source.readFile startupFile⟩ := by
  rw [logical_projection]
  rfl

#print axioms logical_projection
#print axioms source_site68
#print axioms sourceEntry_matches_file
end PA213.PA.Startup

