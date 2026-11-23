module
public import I3_334.Search.SearchProgram
public import I3_334.Simulation.ReferenceTree
public import I3_334Support.Search.Compiler.Factorization
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380.Compiler

-- Compare normalized sequences, rather than materializing certificates
-- for every path through the shared read-only decoder.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 24000000 in
set_option cbv.maxSteps 4000000 in
theorem reference_normalized_eq : normalize PalomarI3334.referenceProgram = normalize main :=
  sameProgram_sound (by cbv)

theorem reference_matches_source : Equivalent PalomarI3334.referenceProgram main :=
  equivalent_of_normalized reference_normalized_eq

end PalomarI3334.SearchProgram
