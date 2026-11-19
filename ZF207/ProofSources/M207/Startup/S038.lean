module
public import M207.Startup.Data
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace M207.Startup
open M6.Zip
theorem run0456 : run literal 128 c0456 = some c0457 := by decide +kernel
theorem run0457 : run literal 120 c0457 = some c0458 := by decide +kernel
end M207.Startup
