module
public import M209.SourceEndpoint
public import M209.SourceProjection
public import M209.SourceProjectionTransport
@[expose] public section
namespace M209.Source
open SourceSimulation M6.Zip

theorem next_projection (s : State) (hs : Valid 4341 s) :
    scalarNext program (project s) = (next program s).map project := by
  obtain ⟨code,hget,hbound,himpl⟩ := Coverage.complete s.pc hs.1
  simp only [scalarNext,next,project,hget,Option.bind_some]
  exact execute_projection hbound hs

/-- Gap and spare registers have no effect on source termination; all nine
addressed registers are retained, in the fixed physical permutation. -/
theorem termination_ignores_gap_and_spares (s : State) (hs : Valid 4341 s) :
    Terminates (next program) s ↔ Terminates (scalarNext program) (project s) :=
  termination_projection (next program) (scalarNext program) project (Valid 4341)
    Coverage.implementation.preserve next_projection s hs

/-- Nine-register resolved-CFG endpoint, with no tape-gap or spare-file data. -/
theorem blank_halts_iff_nine_register_cfg :
    Halts literal (zc 0 [] []) ↔ Terminates (scalarNext program) (project initialState) :=
  blank_halts_iff_cfg.trans (termination_ignores_gap_and_spares initialState initial_valid)

end M209.Source
