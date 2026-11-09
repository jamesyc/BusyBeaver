module

public import PA213.SourceCheck

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.SourceCheckShards.S014
theorem checked : PA213.SourceCheck.rangeCheck 896 64 = true := by decide +kernel
end PA213.SourceCheckShards.S014
