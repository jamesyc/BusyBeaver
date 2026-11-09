module

public import PA213.FastSourceCheck

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.SourceCheckShards.S053
theorem checked : PA213.FastSourceCheck.check 3392 64 = true := by decide +kernel
end PA213.SourceCheckShards.S053
