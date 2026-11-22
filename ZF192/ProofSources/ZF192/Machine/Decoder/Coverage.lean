module
public import ZF192.Machine.Decoder.Coverage.Range00
public import ZF192.Machine.Decoder.Coverage.Range01
public import ZF192.Machine.Decoder.Coverage.Range02
public import ZF192.Machine.Decoder.Coverage.Range03
public import ZF192.Machine.Decoder.Coverage.Range04
public import ZF192.Machine.Decoder.Coverage.Range05
public import ZF192.Machine.Decoder.Coverage.Range06
public import ZF192.Machine.Decoder.Coverage.Range07
public import ZF192.Machine.Decoder.Coverage.Range08
public import ZF192.Machine.Decoder.Coverage.Range09
public import ZF192.Machine.Decoder.Coverage.Range10
public import ZF192.Machine.Decoder.Coverage.Range11
public import ZF192.Machine.Decoder.Coverage.Range12
public import ZF192.Machine.Decoder.Coverage.Range13
public import ZF192.Machine.Decoder.Coverage.Range14

namespace M192.Sites
open M192.FiniteChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Every live source instruction passes its program-window check. -/
public theorem allChecked : blockCheck 0 3689 = true :=
  join_blocks siteCheck 256 3689 [
    checked00, checked01, checked02, checked03, checked04, checked05,
    checked06, checked07, checked08, checked09, checked10, checked11,
    checked12, checked13, checked14]

end M192.Sites
