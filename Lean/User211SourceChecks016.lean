import User211SourceChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.Source.Checks016
theorem checked : PA211.UserCandidate.Source.blockCheck 1024 64=true := by decide +kernel
end PA211.UserCandidate.Source.Checks016
