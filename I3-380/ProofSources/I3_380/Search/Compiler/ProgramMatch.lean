module
public import I3_380.Search.Compiler.Backward
public import I3_380.Search.Compiler.Factorization
public import I3_380.Search.Compiler.Reference
public import I3_380.Search.Compiler.Source
@[expose] public section

namespace PalomarI3380.Compiler

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
set_option cbv.maxSteps 2000000 in
/-- Compare the decoded register tree with the independently constructed
source program after scoped sequence reassociation and increment sorting. -/
theorem reference_normalized_eq : normalize referenceProgram = normalize Source.main :=
  sameProgram_sound (by cbv)

theorem reference_matches_source : Equivalent referenceProgram Source.main :=
  equivalent_of_normalized reference_normalized_eq

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
private theorem source_closed : Source.main.closed := by
  unfold Program.closed
  decide +kernel

private theorem reference_closed : referenceProgram.closed := by
  unfold Program.closed
  rw [← normalize_needs referenceProgram, reference_normalized_eq, normalize_needs]
  exact source_closed

theorem literal_halts_iff_source :
    HaltsFrom machine blank ↔ IteratesToHalt Source.main (fun _ => 0) :=
  literal_halts_iff_reference_program.trans
    ((halts_iff_iterations referenceProgram reference_closed _).trans (reference_matches_source.iterates _))

end PalomarI3380.Compiler
