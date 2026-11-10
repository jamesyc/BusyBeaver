import PA213.SourceCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.SourceCheckShards.S017
theorem checked : PA213.SourceCheck.rangeCheck 1088 64 = true := by decide +kernel
end PA213.SourceCheckShards.S017
