import User211ModelCoverage
import User211ModelCoverageAssembler
namespace PA211.UserCandidate.PA.CompleteModelCoverage
open PA215.Source PA211.UserCandidate.PA.ModelCoverage
/-- Exact original source instructions at the reconstructed candidate paths,
implemented in every PA model by the literal minimized211 table. -/
theorem coverage : ∀ i, i<3947 → ∃ code, resolveAt exactSites i=some code ∧
    ModelPrimitive.Implements PA211.UserCandidate.Source.path 3947
      (PA211.UserCandidate.Source.path i) code :=
  ModelCoverageAssembler.coverage_of_entries entries sites_eq codes_eq
#print axioms coverage
end PA211.UserCandidate.PA.CompleteModelCoverage
