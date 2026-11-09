import PA211.UserCandidate.Dense
import PA211.UserCandidate.LiteralStartup
import PA211.UserCandidate.StateBound
import PA211.UserCandidate.StartupExact
import PA211.UserCandidate.NonhaltingFromSource
namespace PA211.UserCandidate
open PA215.Zip PA215.Source

theorem physical_endpoint
    (h : ¬ CycleHalts exactSites ⟨.at 68,readFile PA213.Startup.startupFile⟩) :
    CandidateTable.workingLabels.length = 211 ∧
    CandidateTable.workingLabels.Nodup ∧
    CandidateTable.workingDense.length * 2 = 422 ∧
    run CandidateTable.machine 64764 PA213.Startup.blank = some PA213.Startup.startupTarget ∧
    ¬ Halts Dense.machine (zc 0 [] []) :=
  ⟨CandidateTable.working_count,CandidateTable.working_nodup,Dense.defined_row_count,
    Startup.startup_exact,NonhaltingFromSource.literal_blank_nonhalting h⟩

#print axioms CandidateTable.native_boxes
#print axioms StateBound.domain
#print axioms CompleteCoverage.coverage
#print axioms Startup.startup_exact
#print axioms LiteralStartup.startup_exact
#print axioms physical_endpoint
end PA211.UserCandidate
