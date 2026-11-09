module

public import PA213.SourceData.Instructions
public import PA213.SourceData.Successors

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.SourceData
theorem site_count : sitePaths.size = 3947 := by decide +kernel
theorem op_count : siteOps.size = 3947 := by decide +kernel
end PA213.SourceData
