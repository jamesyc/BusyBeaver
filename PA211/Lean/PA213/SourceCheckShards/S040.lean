import PA213.FastSourceCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.SourceCheckShards.S040
theorem checked : PA213.FastSourceCheck.check 2560 64 = true := by decide +kernel
end PA213.SourceCheckShards.S040
