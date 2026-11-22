module
public import ZF192.Machine.Startup.Checkpoints

namespace M192.Startup

set_option maxRecDepth 40000 in
set_option maxHeartbeats 64000000 in
public theorem chunk5 : packedRun 8837 checkpoint4 = some checkpoint5 := by
  decide +kernel

end M192.Startup
