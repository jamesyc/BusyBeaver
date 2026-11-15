module
public import M209.SourceInitial
public import M209.SourceCoverage
@[expose] public section
namespace M209.Source
open M6.Zip

/-- Literal209 blank-start halting is equivalent to halting of the exact
recovered resolved CFG at ordinal25, with the entire35-entry initial file.
Formal source-tree-to-CFG compilation is a separate obligation. -/
theorem blank_halts_iff_cfg :
    Halts literal (zc 0 [] []) ↔ SourceSimulation.Terminates (next program) initialState := by
  constructor
  · intro h
    exact (Coverage.source_halts_iff initialState initial_valid).mp
      (SourceSimulation.halt_after_reach blank_to_cfg h)
  · intro h
    exact ((Coverage.source_halts_iff initialState initial_valid).mpr h).of_reach blank_to_cfg
end M209.Source
