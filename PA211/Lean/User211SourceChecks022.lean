import User211SourceChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.Source.Checks022
theorem checked : PA211.UserCandidate.Source.blockCheck 1408 64=true := by decide +kernel
end PA211.UserCandidate.Source.Checks022
