import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S046
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2265_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2265_plain_checked : check 391 s2265_plain_contract = true := by decide +kernel
def s2265_plain : CertifiedContract :=
  ⟨2265, 2266, 0, (.inc 2), s2265_plain_contract, 391, s2265_plain_checked⟩

def s2266_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2266_plain_checked : check 107 s2266_plain_contract = true := by decide +kernel
def s2266_plain : CertifiedContract :=
  ⟨2266, 2264, 0, .none, s2266_plain_contract, 107, s2266_plain_checked⟩

def s2267_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2267_plain_checked : check 110 s2267_plain_contract = true := by decide +kernel
def s2267_plain : CertifiedContract :=
  ⟨2267, 2258, 0, .none, s2267_plain_contract, 110, s2267_plain_checked⟩

def s2268_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false] 0 .none⟩
theorem s2268_zero_checked : check 360 s2268_zero_contract = true := by decide +kernel
def s2268_zero : CertifiedContract :=
  ⟨2268, 2274, 0, .none, s2268_zero_contract, 360, s2268_zero_checked⟩

def s2268_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2268_positive_checked : check 360 s2268_positive_contract = true := by decide +kernel
def s2268_positive : CertifiedContract :=
  ⟨2268, 2269, 1, (.dec 5), s2268_positive_contract, 360, s2268_positive_checked⟩

def s2269_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2269_plain_checked : check 373 s2269_plain_contract = true := by decide +kernel
def s2269_plain : CertifiedContract :=
  ⟨2269, 2270, 0, (.inc 2), s2269_plain_contract, 373, s2269_plain_checked⟩

def s2270_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2270_plain_checked : check 376 s2270_plain_contract = true := by decide +kernel
def s2270_plain : CertifiedContract :=
  ⟨2270, 2271, 0, (.inc 2), s2270_plain_contract, 376, s2270_plain_checked⟩

def s2271_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2271_plain_checked : check 382 s2271_plain_contract = true := by decide +kernel
def s2271_plain : CertifiedContract :=
  ⟨2271, 2272, 0, (.inc 2), s2271_plain_contract, 382, s2271_plain_checked⟩

def s2272_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2272_plain_checked : check 388 s2272_plain_contract = true := by decide +kernel
def s2272_plain : CertifiedContract :=
  ⟨2272, 2273, 0, (.inc 2), s2272_plain_contract, 388, s2272_plain_checked⟩

def s2273_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s2273_plain_checked : check 95 s2273_plain_contract = true := by decide +kernel
def s2273_plain : CertifiedContract :=
  ⟨2273, 2268, 0, .none, s2273_plain_contract, 95, s2273_plain_checked⟩

def s2274_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2274_plain_checked : check 328 s2274_plain_contract = true := by decide +kernel
def s2274_plain : CertifiedContract :=
  ⟨2274, 2275, 0, (.inc 2), s2274_plain_contract, 328, s2274_plain_checked⟩

def s2275_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s2275_plain_checked : check 337 s2275_plain_contract = true := by decide +kernel
def s2275_plain : CertifiedContract :=
  ⟨2275, 2276, 0, (.inc 2), s2275_plain_contract, 337, s2275_plain_checked⟩

def s2276_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2276_zero_checked : check 345 s2276_zero_contract = true := by decide +kernel
def s2276_zero : CertifiedContract :=
  ⟨2276, 2279, 0, .none, s2276_zero_contract, 345, s2276_zero_checked⟩

def s2276_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2276_positive_checked : check 351 s2276_positive_contract = true := by decide +kernel
def s2276_positive : CertifiedContract :=
  ⟨2276, 2277, 1, (.dec 2), s2276_positive_contract, 351, s2276_positive_checked⟩

def s2277_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2277_plain_checked : check 364 s2277_plain_contract = true := by decide +kernel
def s2277_plain : CertifiedContract :=
  ⟨2277, 2278, 0, (.inc 8), s2277_plain_contract, 364, s2277_plain_checked⟩

def s2278_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s2278_plain_checked : check 95 s2278_plain_contract = true := by decide +kernel
def s2278_plain : CertifiedContract :=
  ⟨2278, 2276, 0, .none, s2278_plain_contract, 95, s2278_plain_checked⟩

def s2279_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2279_zero_checked : check 366 s2279_zero_contract = true := by decide +kernel
def s2279_zero : CertifiedContract :=
  ⟨2279, 2282, 0, .none, s2279_zero_contract, 366, s2279_zero_checked⟩

def s2279_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2279_positive_checked : check 372 s2279_positive_contract = true := by decide +kernel
def s2279_positive : CertifiedContract :=
  ⟨2279, 2280, 1, (.dec 0), s2279_positive_contract, 372, s2279_positive_checked⟩

def s2280_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2280_plain_checked : check 364 s2280_plain_contract = true := by decide +kernel
def s2280_plain : CertifiedContract :=
  ⟨2280, 2281, 0, (.inc 2), s2280_plain_contract, 364, s2280_plain_checked⟩

def s2281_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2281_plain_checked : check 98 s2281_plain_contract = true := by decide +kernel
def s2281_plain : CertifiedContract :=
  ⟨2281, 2279, 0, .none, s2281_plain_contract, 98, s2281_plain_checked⟩

def s2282_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2282_zero_checked : check 372 s2282_zero_contract = true := by decide +kernel
def s2282_zero : CertifiedContract :=
  ⟨2282, 2286, 0, .none, s2282_zero_contract, 372, s2282_zero_checked⟩

def s2282_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2282_positive_checked : check 378 s2282_positive_contract = true := by decide +kernel
def s2282_positive : CertifiedContract :=
  ⟨2282, 2283, 1, (.dec 2), s2282_positive_contract, 378, s2282_positive_checked⟩

def s2283_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2283_plain_checked : check 391 s2283_plain_contract = true := by decide +kernel
def s2283_plain : CertifiedContract :=
  ⟨2283, 2284, 0, (.inc 5), s2283_plain_contract, 391, s2283_plain_checked⟩

def s2284_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2284_plain_checked : check 418 s2284_plain_contract = true := by decide +kernel
def s2284_plain : CertifiedContract :=
  ⟨2284, 2285, 0, (.inc 8), s2284_plain_contract, 418, s2284_plain_checked⟩

def s2285_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2285_plain_checked : check 113 s2285_plain_contract = true := by decide +kernel
def s2285_plain : CertifiedContract :=
  ⟨2285, 2282, 0, .none, s2285_plain_contract, 113, s2285_plain_checked⟩

def s2286_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2286_zero_checked : check 393 s2286_zero_contract = true := by decide +kernel
def s2286_zero : CertifiedContract :=
  ⟨2286, 2292, 0, .none, s2286_zero_contract, 393, s2286_zero_checked⟩

def s2286_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2286_positive_checked : check 396 s2286_positive_contract = true := by decide +kernel
def s2286_positive : CertifiedContract :=
  ⟨2286, 2287, 1, (.dec 8), s2286_positive_contract, 396, s2286_positive_checked⟩

def s2287_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2287_plain_checked : check 391 s2287_plain_contract = true := by decide +kernel
def s2287_plain : CertifiedContract :=
  ⟨2287, 2288, 0, (.inc 5), s2287_plain_contract, 391, s2287_plain_checked⟩

def s2288_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2288_zero_checked : check 411 s2288_zero_contract = true := by decide +kernel
def s2288_zero : CertifiedContract :=
  ⟨2288, 2291, 0, .none, s2288_zero_contract, 411, s2288_zero_checked⟩

def s2288_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2288_positive_checked : check 414 s2288_positive_contract = true := by decide +kernel
def s2288_positive : CertifiedContract :=
  ⟨2288, 2289, 1, (.dec 8), s2288_positive_contract, 414, s2288_positive_checked⟩

def s2289_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2289_plain_checked : check 409 s2289_plain_contract = true := by decide +kernel
def s2289_plain : CertifiedContract :=
  ⟨2289, 2290, 0, (.inc 2), s2289_plain_contract, 409, s2289_plain_checked⟩

def s2290_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2290_plain_checked : check 113 s2290_plain_contract = true := by decide +kernel
def s2290_plain : CertifiedContract :=
  ⟨2290, 2288, 0, .none, s2290_plain_contract, 113, s2290_plain_checked⟩

def s2291_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2291_plain_checked : check 116 s2291_plain_contract = true := by decide +kernel
def s2291_plain : CertifiedContract :=
  ⟨2291, 2282, 0, .none, s2291_plain_contract, 116, s2291_plain_checked⟩

def s2292_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s2292_zero_checked : check 381 s2292_zero_contract = true := by decide +kernel
def s2292_zero : CertifiedContract :=
  ⟨2292, 2295, 0, .none, s2292_zero_contract, 381, s2292_zero_checked⟩

def s2292_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2292_positive_checked : check 378 s2292_positive_contract = true := by decide +kernel
def s2292_positive : CertifiedContract :=
  ⟨2292, 2293, 1, (.dec 5), s2292_positive_contract, 378, s2292_positive_checked⟩

def s2293_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2293_plain_checked : check 391 s2293_plain_contract = true := by decide +kernel
def s2293_plain : CertifiedContract :=
  ⟨2293, 2294, 0, (.inc 0), s2293_plain_contract, 391, s2293_plain_checked⟩

def s2294_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2294_plain_checked : check 104 s2294_plain_contract = true := by decide +kernel
def s2294_plain : CertifiedContract :=
  ⟨2294, 2292, 0, .none, s2294_plain_contract, 104, s2294_plain_checked⟩

def s2295_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2295_zero_checked : check 345 s2295_zero_contract = true := by decide +kernel
def s2295_zero : CertifiedContract :=
  ⟨2295, 2299, 0, .none, s2295_zero_contract, 345, s2295_zero_checked⟩

def s2295_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s2295_positive_checked : check 351 s2295_positive_contract = true := by decide +kernel
def s2295_positive : CertifiedContract :=
  ⟨2295, 2296, 1, (.dec 3), s2295_positive_contract, 351, s2295_positive_checked⟩

def s2296_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2296_plain_checked : check 364 s2296_plain_contract = true := by decide +kernel
def s2296_plain : CertifiedContract :=
  ⟨2296, 2297, 0, (.inc 2), s2296_plain_contract, 364, s2296_plain_checked⟩

def s2297_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2297_plain_checked : check 391 s2297_plain_contract = true := by decide +kernel
def s2297_plain : CertifiedContract :=
  ⟨2297, 2298, 0, (.inc 8), s2297_plain_contract, 391, s2297_plain_checked⟩

def s2298_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s2298_plain_checked : check 104 s2298_plain_contract = true := by decide +kernel
def s2298_plain : CertifiedContract :=
  ⟨2298, 2295, 0, .none, s2298_plain_contract, 104, s2298_plain_checked⟩

def s2299_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2299_zero_checked : check 351 s2299_zero_contract = true := by decide +kernel
def s2299_zero : CertifiedContract :=
  ⟨2299, 2302, 0, .none, s2299_zero_contract, 351, s2299_zero_checked⟩

def s2299_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s2299_positive_checked : check 351 s2299_positive_contract = true := by decide +kernel
def s2299_positive : CertifiedContract :=
  ⟨2299, 2300, 1, (.dec 8), s2299_positive_contract, 351, s2299_positive_checked⟩

def s2300_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s2300_plain_checked : check 367 s2300_plain_contract = true := by decide +kernel
def s2300_plain : CertifiedContract :=
  ⟨2300, 2301, 0, (.inc 3), s2300_plain_contract, 367, s2300_plain_checked⟩

def s2301_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2301_plain_checked : check 95 s2301_plain_contract = true := by decide +kernel
def s2301_plain : CertifiedContract :=
  ⟨2301, 2299, 0, .none, s2301_plain_contract, 95, s2301_plain_checked⟩

def s2302_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2302_zero_checked : check 345 s2302_zero_contract = true := by decide +kernel
def s2302_zero : CertifiedContract :=
  ⟨2302, 2305, 0, .none, s2302_zero_contract, 345, s2302_zero_checked⟩

def s2302_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2302_positive_checked : check 351 s2302_positive_contract = true := by decide +kernel
def s2302_positive : CertifiedContract :=
  ⟨2302, 2303, 1, (.dec 2), s2302_positive_contract, 351, s2302_positive_checked⟩

def s2303_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2303_plain_checked : check 364 s2303_plain_contract = true := by decide +kernel
def s2303_plain : CertifiedContract :=
  ⟨2303, 2304, 0, (.inc 8), s2303_plain_contract, 364, s2303_plain_checked⟩

def s2304_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2304_plain_checked : check 95 s2304_plain_contract = true := by decide +kernel
def s2304_plain : CertifiedContract :=
  ⟨2304, 2302, 0, .none, s2304_plain_contract, 95, s2304_plain_checked⟩

def s2305_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2305_zero_checked : check 366 s2305_zero_contract = true := by decide +kernel
def s2305_zero : CertifiedContract :=
  ⟨2305, 2308, 0, .none, s2305_zero_contract, 366, s2305_zero_checked⟩

def s2305_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2305_positive_checked : check 372 s2305_positive_contract = true := by decide +kernel
def s2305_positive : CertifiedContract :=
  ⟨2305, 2306, 1, (.dec 0), s2305_positive_contract, 372, s2305_positive_checked⟩

def s2306_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2306_plain_checked : check 364 s2306_plain_contract = true := by decide +kernel
def s2306_plain : CertifiedContract :=
  ⟨2306, 2307, 0, (.inc 2), s2306_plain_contract, 364, s2306_plain_checked⟩

def s2307_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2307_plain_checked : check 98 s2307_plain_contract = true := by decide +kernel
def s2307_plain : CertifiedContract :=
  ⟨2307, 2305, 0, .none, s2307_plain_contract, 98, s2307_plain_checked⟩

def s2308_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2308_zero_checked : check 372 s2308_zero_contract = true := by decide +kernel
def s2308_zero : CertifiedContract :=
  ⟨2308, 2312, 0, .none, s2308_zero_contract, 372, s2308_zero_checked⟩

def s2308_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2308_positive_checked : check 378 s2308_positive_contract = true := by decide +kernel
def s2308_positive : CertifiedContract :=
  ⟨2308, 2309, 1, (.dec 2), s2308_positive_contract, 378, s2308_positive_checked⟩

def s2309_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2309_plain_checked : check 391 s2309_plain_contract = true := by decide +kernel
def s2309_plain : CertifiedContract :=
  ⟨2309, 2310, 0, (.inc 5), s2309_plain_contract, 391, s2309_plain_checked⟩

def s2310_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2310_plain_checked : check 418 s2310_plain_contract = true := by decide +kernel
def s2310_plain : CertifiedContract :=
  ⟨2310, 2311, 0, (.inc 8), s2310_plain_contract, 418, s2310_plain_checked⟩

def s2311_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2311_plain_checked : check 113 s2311_plain_contract = true := by decide +kernel
def s2311_plain : CertifiedContract :=
  ⟨2311, 2308, 0, .none, s2311_plain_contract, 113, s2311_plain_checked⟩

def s2312_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2312_zero_checked : check 393 s2312_zero_contract = true := by decide +kernel
def s2312_zero : CertifiedContract :=
  ⟨2312, 2318, 0, .none, s2312_zero_contract, 393, s2312_zero_checked⟩

def s2312_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2312_positive_checked : check 396 s2312_positive_contract = true := by decide +kernel
def s2312_positive : CertifiedContract :=
  ⟨2312, 2313, 1, (.dec 8), s2312_positive_contract, 396, s2312_positive_checked⟩

def s2313_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2313_plain_checked : check 391 s2313_plain_contract = true := by decide +kernel
def s2313_plain : CertifiedContract :=
  ⟨2313, 2314, 0, (.inc 5), s2313_plain_contract, 391, s2313_plain_checked⟩

def s2314_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2314_zero_checked : check 411 s2314_zero_contract = true := by decide +kernel
def s2314_zero : CertifiedContract :=
  ⟨2314, 2317, 0, .none, s2314_zero_contract, 411, s2314_zero_checked⟩

def s2314_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2314_positive_checked : check 414 s2314_positive_contract = true := by decide +kernel
def s2314_positive : CertifiedContract :=
  ⟨2314, 2315, 1, (.dec 8), s2314_positive_contract, 414, s2314_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S046
