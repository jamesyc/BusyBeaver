module
public import M209.Startup.Data
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace M209.Startup
open M6.Zip
theorem run0000 : run literal 128 c0000 = some c0001 := by decide +kernel
theorem run0001 : run literal 128 c0001 = some c0002 := by decide +kernel
theorem run0002 : run literal 128 c0002 = some c0003 := by decide +kernel
theorem run0003 : run literal 128 c0003 = some c0004 := by decide +kernel
theorem run0004 : run literal 128 c0004 = some c0005 := by decide +kernel
theorem run0005 : run literal 128 c0005 = some c0006 := by decide +kernel
theorem run0006 : run literal 128 c0006 = some c0007 := by decide +kernel
theorem run0007 : run literal 128 c0007 = some c0008 := by decide +kernel
theorem run0008 : run literal 128 c0008 = some c0009 := by decide +kernel
theorem run0009 : run literal 128 c0009 = some c0010 := by decide +kernel
theorem run0010 : run literal 128 c0010 = some c0011 := by decide +kernel
theorem run0011 : run literal 128 c0011 = some c0012 := by decide +kernel
end M209.Startup
