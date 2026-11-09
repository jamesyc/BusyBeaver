module

public import PA213.FastSourceCheck

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.SourceCheckShards.S036
theorem checked : PA213.FastSourceCheck.check 2304 64 = true := by decide +kernel
end PA213.SourceCheckShards.S036
