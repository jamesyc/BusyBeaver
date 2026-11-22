module
public import ZF192.Machine.Startup.Checkpoints

namespace M192.Startup

set_option maxRecDepth 40000 in
set_option maxHeartbeats 64000000 in
public theorem chunk3 : packedRun 8836 checkpoint2 = some checkpoint3 := by
  decide +kernel

end M192.Startup
