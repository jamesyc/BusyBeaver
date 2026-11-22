module
public import ZF192.Machine.Decoder.Sites

open M192.Sites M192.FiniteChecks
set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
public theorem M192.Sites.checked14 : blockCheck 3584 105 = true :=
  check_block siteCheck 3584 105
