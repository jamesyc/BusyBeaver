module
public import ZF192.Machine.Control.Checks
public import ZF192.Machine.FiniteChecks

namespace M192.Control
open M192.FiniteChecks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
public theorem aligned06 : block check 1536 256 = true :=
  check_block check 1536 256

end M192.Control
