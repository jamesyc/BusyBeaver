module

public import User211SourceChecks

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.Source.Checks002
theorem checked : PA211.UserCandidate.Source.blockCheck 128 64=true := by decide +kernel
end PA211.UserCandidate.Source.Checks002
