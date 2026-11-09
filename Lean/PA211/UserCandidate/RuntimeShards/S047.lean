import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S047
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2315_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2315_plain_checked : check 409 s2315_plain_contract = true := by decide +kernel
def s2315_plain : CertifiedContract :=
  ⟨2315, 2316, 0, (.inc 2), s2315_plain_contract, 409, s2315_plain_checked⟩

def s2316_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2316_plain_checked : check 113 s2316_plain_contract = true := by decide +kernel
def s2316_plain : CertifiedContract :=
  ⟨2316, 2314, 0, .none, s2316_plain_contract, 113, s2316_plain_checked⟩

def s2317_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2317_plain_checked : check 116 s2317_plain_contract = true := by decide +kernel
def s2317_plain : CertifiedContract :=
  ⟨2317, 2308, 0, .none, s2317_plain_contract, 116, s2317_plain_checked⟩

def s2318_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s2318_zero_checked : check 381 s2318_zero_contract = true := by decide +kernel
def s2318_zero : CertifiedContract :=
  ⟨2318, 2321, 0, .none, s2318_zero_contract, 381, s2318_zero_checked⟩

def s2318_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2318_positive_checked : check 378 s2318_positive_contract = true := by decide +kernel
def s2318_positive : CertifiedContract :=
  ⟨2318, 2319, 1, (.dec 5), s2318_positive_contract, 378, s2318_positive_checked⟩

def s2319_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2319_plain_checked : check 391 s2319_plain_contract = true := by decide +kernel
def s2319_plain : CertifiedContract :=
  ⟨2319, 2320, 0, (.inc 0), s2319_plain_contract, 391, s2319_plain_checked⟩

def s2320_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2320_plain_checked : check 104 s2320_plain_contract = true := by decide +kernel
def s2320_plain : CertifiedContract :=
  ⟨2320, 2318, 0, .none, s2320_plain_contract, 104, s2320_plain_checked⟩

def s2321_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2321_zero_checked : check 345 s2321_zero_contract = true := by decide +kernel
def s2321_zero : CertifiedContract :=
  ⟨2321, 2325, 0, .none, s2321_zero_contract, 345, s2321_zero_checked⟩

def s2321_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, true, false] 1 (.dec 4)⟩
theorem s2321_positive_checked : check 351 s2321_positive_contract = true := by decide +kernel
def s2321_positive : CertifiedContract :=
  ⟨2321, 2322, 1, (.dec 4), s2321_positive_contract, 351, s2321_positive_checked⟩

def s2322_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2322_plain_checked : check 364 s2322_plain_contract = true := by decide +kernel
def s2322_plain : CertifiedContract :=
  ⟨2322, 2323, 0, (.inc 2), s2322_plain_contract, 364, s2322_plain_checked⟩

def s2323_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2323_plain_checked : check 391 s2323_plain_contract = true := by decide +kernel
def s2323_plain : CertifiedContract :=
  ⟨2323, 2324, 0, (.inc 8), s2323_plain_contract, 391, s2323_plain_checked⟩

def s2324_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s2324_plain_checked : check 104 s2324_plain_contract = true := by decide +kernel
def s2324_plain : CertifiedContract :=
  ⟨2324, 2321, 0, .none, s2324_plain_contract, 104, s2324_plain_checked⟩

def s2325_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s2325_zero_checked : check 354 s2325_zero_contract = true := by decide +kernel
def s2325_zero : CertifiedContract :=
  ⟨2325, 2328, 0, .none, s2325_zero_contract, 354, s2325_zero_checked⟩

def s2325_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2325_positive_checked : check 351 s2325_positive_contract = true := by decide +kernel
def s2325_positive : CertifiedContract :=
  ⟨2325, 2326, 1, (.dec 8), s2325_positive_contract, 351, s2325_positive_checked⟩

def s2326_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, true, true] 0 (.inc 4)⟩
theorem s2326_plain_checked : check 355 s2326_plain_contract = true := by decide +kernel
def s2326_plain : CertifiedContract :=
  ⟨2326, 2327, 0, (.inc 4), s2326_plain_contract, 355, s2326_plain_checked⟩

def s2327_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2327_plain_checked : check 95 s2327_plain_contract = true := by decide +kernel
def s2327_plain : CertifiedContract :=
  ⟨2327, 2325, 0, .none, s2327_plain_contract, 95, s2327_plain_checked⟩

def s2328_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s2328_zero_checked : check 357 s2328_zero_contract = true := by decide +kernel
def s2328_zero : CertifiedContract :=
  ⟨2328, 2336, 0, .none, s2328_zero_contract, 357, s2328_zero_checked⟩

def s2328_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2328_positive_checked : check 363 s2328_positive_contract = true := by decide +kernel
def s2328_positive : CertifiedContract :=
  ⟨2328, 2329, 1, (.dec 0), s2328_positive_contract, 363, s2328_positive_checked⟩

def s2329_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2329_plain_checked : check 373 s2329_plain_contract = true := by decide +kernel
def s2329_plain : CertifiedContract :=
  ⟨2329, 2330, 0, (.inc 5), s2329_plain_contract, 373, s2329_plain_checked⟩

def s2330_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2330_zero_checked : check 399 s2330_zero_contract = true := by decide +kernel
def s2330_zero : CertifiedContract :=
  ⟨2330, 2332, 0, .none, s2330_zero_contract, 399, s2330_zero_checked⟩

def s2330_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2330_positive_checked : check 405 s2330_positive_contract = true := by decide +kernel
def s2330_positive : CertifiedContract :=
  ⟨2330, 2331, 1, (.dec 8), s2330_positive_contract, 405, s2330_positive_checked⟩

def s2331_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2331_plain_checked : check 110 s2331_plain_contract = true := by decide +kernel
def s2331_plain : CertifiedContract :=
  ⟨2331, 2335, 0, .none, s2331_plain_contract, 110, s2331_plain_checked⟩

def s2332_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2332_zero_checked : check 411 s2332_zero_contract = true := by decide +kernel
def s2332_zero : CertifiedContract :=
  ⟨2332, 2335, 0, .none, s2332_zero_contract, 411, s2332_zero_checked⟩

def s2332_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2332_positive_checked : check 414 s2332_positive_contract = true := by decide +kernel
def s2332_positive : CertifiedContract :=
  ⟨2332, 2333, 1, (.dec 5), s2332_positive_contract, 414, s2332_positive_checked⟩

def s2333_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2333_plain_checked : check 418 s2333_plain_contract = true := by decide +kernel
def s2333_plain : CertifiedContract :=
  ⟨2333, 2334, 0, (.inc 8), s2333_plain_contract, 418, s2333_plain_checked⟩

def s2334_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2334_plain_checked : check 113 s2334_plain_contract = true := by decide +kernel
def s2334_plain : CertifiedContract :=
  ⟨2334, 2332, 0, .none, s2334_plain_contract, 113, s2334_plain_checked⟩

def s2335_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s2335_plain_checked : check 104 s2335_plain_contract = true := by decide +kernel
def s2335_plain : CertifiedContract :=
  ⟨2335, 2328, 0, .none, s2335_plain_contract, 104, s2335_plain_checked⟩

def s2336_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2336_zero_checked : check 357 s2336_zero_contract = true := by decide +kernel
def s2336_zero : CertifiedContract :=
  ⟨2336, 2339, 0, .none, s2336_zero_contract, 357, s2336_zero_checked⟩

def s2336_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2336_positive_checked : check 360 s2336_positive_contract = true := by decide +kernel
def s2336_positive : CertifiedContract :=
  ⟨2336, 2337, 1, (.dec 5), s2336_positive_contract, 360, s2336_positive_checked⟩

def s2337_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2337_plain_checked : check 373 s2337_plain_contract = true := by decide +kernel
def s2337_plain : CertifiedContract :=
  ⟨2337, 2338, 0, (.inc 0), s2337_plain_contract, 373, s2337_plain_checked⟩

def s2338_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s2338_plain_checked : check 98 s2338_plain_contract = true := by decide +kernel
def s2338_plain : CertifiedContract :=
  ⟨2338, 2336, 0, .none, s2338_plain_contract, 98, s2338_plain_checked⟩

def s2339_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s2339_zero_checked : check 354 s2339_zero_contract = true := by decide +kernel
def s2339_zero : CertifiedContract :=
  ⟨2339, 2343, 0, .none, s2339_zero_contract, 354, s2339_zero_checked⟩

def s2339_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2339_positive_checked : check 360 s2339_positive_contract = true := by decide +kernel
def s2339_positive : CertifiedContract :=
  ⟨2339, 2340, 1, (.dec 2), s2339_positive_contract, 360, s2339_positive_checked⟩

def s2340_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2340_plain_checked : check 373 s2340_plain_contract = true := by decide +kernel
def s2340_plain : CertifiedContract :=
  ⟨2340, 2341, 0, (.inc 5), s2340_plain_contract, 373, s2340_plain_checked⟩

def s2341_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2341_plain_checked : check 400 s2341_plain_contract = true := by decide +kernel
def s2341_plain : CertifiedContract :=
  ⟨2341, 2342, 0, (.inc 8), s2341_plain_contract, 400, s2341_plain_checked⟩

def s2342_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2342_plain_checked : check 107 s2342_plain_contract = true := by decide +kernel
def s2342_plain : CertifiedContract :=
  ⟨2342, 2339, 0, .none, s2342_plain_contract, 107, s2342_plain_checked⟩

def s2343_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s2343_zero_checked : check 375 s2343_zero_contract = true := by decide +kernel
def s2343_zero : CertifiedContract :=
  ⟨2343, 2349, 0, .none, s2343_zero_contract, 375, s2343_zero_checked⟩

def s2343_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2343_positive_checked : check 378 s2343_positive_contract = true := by decide +kernel
def s2343_positive : CertifiedContract :=
  ⟨2343, 2344, 1, (.dec 8), s2343_positive_contract, 378, s2343_positive_checked⟩

def s2344_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2344_plain_checked : check 373 s2344_plain_contract = true := by decide +kernel
def s2344_plain : CertifiedContract :=
  ⟨2344, 2345, 0, (.inc 5), s2344_plain_contract, 373, s2344_plain_checked⟩

def s2345_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s2345_zero_checked : check 393 s2345_zero_contract = true := by decide +kernel
def s2345_zero : CertifiedContract :=
  ⟨2345, 2348, 0, .none, s2345_zero_contract, 393, s2345_zero_checked⟩

def s2345_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2345_positive_checked : check 396 s2345_positive_contract = true := by decide +kernel
def s2345_positive : CertifiedContract :=
  ⟨2345, 2346, 1, (.dec 8), s2345_positive_contract, 396, s2345_positive_checked⟩

def s2346_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2346_plain_checked : check 391 s2346_plain_contract = true := by decide +kernel
def s2346_plain : CertifiedContract :=
  ⟨2346, 2347, 0, (.inc 2), s2346_plain_contract, 391, s2346_plain_checked⟩

def s2347_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2347_plain_checked : check 107 s2347_plain_contract = true := by decide +kernel
def s2347_plain : CertifiedContract :=
  ⟨2347, 2345, 0, .none, s2347_plain_contract, 107, s2347_plain_checked⟩

def s2348_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2348_plain_checked : check 110 s2348_plain_contract = true := by decide +kernel
def s2348_plain : CertifiedContract :=
  ⟨2348, 2339, 0, .none, s2348_plain_contract, 110, s2348_plain_checked⟩

def s2349_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s2349_zero_checked : check 360 s2349_zero_contract = true := by decide +kernel
def s2349_zero : CertifiedContract :=
  ⟨2349, 2355, 0, .none, s2349_zero_contract, 360, s2349_zero_checked⟩

def s2349_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2349_positive_checked : check 360 s2349_positive_contract = true := by decide +kernel
def s2349_positive : CertifiedContract :=
  ⟨2349, 2350, 1, (.dec 5), s2349_positive_contract, 360, s2349_positive_checked⟩

def s2350_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2350_plain_checked : check 373 s2350_plain_contract = true := by decide +kernel
def s2350_plain : CertifiedContract :=
  ⟨2350, 2351, 0, (.inc 2), s2350_plain_contract, 373, s2350_plain_checked⟩

def s2351_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2351_plain_checked : check 376 s2351_plain_contract = true := by decide +kernel
def s2351_plain : CertifiedContract :=
  ⟨2351, 2352, 0, (.inc 2), s2351_plain_contract, 376, s2351_plain_checked⟩

def s2352_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2352_plain_checked : check 382 s2352_plain_contract = true := by decide +kernel
def s2352_plain : CertifiedContract :=
  ⟨2352, 2353, 0, (.inc 2), s2352_plain_contract, 382, s2352_plain_checked⟩

def s2353_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2353_plain_checked : check 388 s2353_plain_contract = true := by decide +kernel
def s2353_plain : CertifiedContract :=
  ⟨2353, 2354, 0, (.inc 2), s2353_plain_contract, 388, s2353_plain_checked⟩

def s2354_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s2354_plain_checked : check 95 s2354_plain_contract = true := by decide +kernel
def s2354_plain : CertifiedContract :=
  ⟨2354, 2349, 0, .none, s2354_plain_contract, 95, s2354_plain_checked⟩

def s2355_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2355_plain_checked : check 328 s2355_plain_contract = true := by decide +kernel
def s2355_plain : CertifiedContract :=
  ⟨2355, 2356, 0, (.inc 2), s2355_plain_contract, 328, s2355_plain_checked⟩

def s2356_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s2356_plain_checked : check 337 s2356_plain_contract = true := by decide +kernel
def s2356_plain : CertifiedContract :=
  ⟨2356, 2357, 0, (.inc 2), s2356_plain_contract, 337, s2356_plain_checked⟩

def s2357_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s2357_zero_checked : check 402 s2357_zero_contract = true := by decide +kernel
def s2357_zero : CertifiedContract :=
  ⟨2357, 2365, 0, .none, s2357_zero_contract, 402, s2357_zero_checked⟩

def s2357_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2357_positive_checked : check 408 s2357_positive_contract = true := by decide +kernel
def s2357_positive : CertifiedContract :=
  ⟨2357, 2358, 1, (.dec 0), s2357_positive_contract, 408, s2357_positive_checked⟩

def s2358_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2358_plain_checked : check 418 s2358_plain_contract = true := by decide +kernel
def s2358_plain : CertifiedContract :=
  ⟨2358, 2359, 0, (.inc 5), s2358_plain_contract, 418, s2358_plain_checked⟩

def s2359_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2359_zero_checked : check 444 s2359_zero_contract = true := by decide +kernel
def s2359_zero : CertifiedContract :=
  ⟨2359, 2361, 0, .none, s2359_zero_contract, 444, s2359_zero_checked⟩

def s2359_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2359_positive_checked : check 450 s2359_positive_contract = true := by decide +kernel
def s2359_positive : CertifiedContract :=
  ⟨2359, 2360, 1, (.dec 8), s2359_positive_contract, 450, s2359_positive_checked⟩

def s2360_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s2360_plain_checked : check 125 s2360_plain_contract = true := by decide +kernel
def s2360_plain : CertifiedContract :=
  ⟨2360, 2364, 0, .none, s2360_plain_contract, 125, s2360_plain_checked⟩

def s2361_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s2361_zero_checked : check 456 s2361_zero_contract = true := by decide +kernel
def s2361_zero : CertifiedContract :=
  ⟨2361, 2364, 0, .none, s2361_zero_contract, 456, s2361_zero_checked⟩

def s2361_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2361_positive_checked : check 459 s2361_positive_contract = true := by decide +kernel
def s2361_positive : CertifiedContract :=
  ⟨2361, 2362, 1, (.dec 5), s2361_positive_contract, 459, s2361_positive_checked⟩

def s2362_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2362_plain_checked : check 463 s2362_plain_contract = true := by decide +kernel
def s2362_plain : CertifiedContract :=
  ⟨2362, 2363, 0, (.inc 8), s2362_plain_contract, 463, s2362_plain_checked⟩

def s2363_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2363_plain_checked : check 128 s2363_plain_contract = true := by decide +kernel
def s2363_plain : CertifiedContract :=
  ⟨2363, 2361, 0, .none, s2363_plain_contract, 128, s2363_plain_checked⟩

def s2364_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s2364_plain_checked : check 119 s2364_plain_contract = true := by decide +kernel
def s2364_plain : CertifiedContract :=
  ⟨2364, 2357, 0, .none, s2364_plain_contract, 119, s2364_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S047
