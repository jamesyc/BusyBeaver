import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S042
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2069_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2069_plain_checked : check 418 s2069_plain_contract = true := by decide +kernel
def s2069_plain : CertifiedContract :=
  ⟨2069, 2070, 0, (.inc 8), s2069_plain_contract, 418, s2069_plain_checked⟩

def s2070_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2070_plain_checked : check 113 s2070_plain_contract = true := by decide +kernel
def s2070_plain : CertifiedContract :=
  ⟨2070, 2067, 0, .none, s2070_plain_contract, 113, s2070_plain_checked⟩

def s2071_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s2071_zero_checked : check 393 s2071_zero_contract = true := by decide +kernel
def s2071_zero : CertifiedContract :=
  ⟨2071, 2077, 0, .none, s2071_zero_contract, 393, s2071_zero_checked⟩

def s2071_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2071_positive_checked : check 396 s2071_positive_contract = true := by decide +kernel
def s2071_positive : CertifiedContract :=
  ⟨2071, 2072, 1, (.dec 8), s2071_positive_contract, 396, s2071_positive_checked⟩

def s2072_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2072_plain_checked : check 391 s2072_plain_contract = true := by decide +kernel
def s2072_plain : CertifiedContract :=
  ⟨2072, 2073, 0, (.inc 5), s2072_plain_contract, 391, s2072_plain_checked⟩

def s2073_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2073_zero_checked : check 411 s2073_zero_contract = true := by decide +kernel
def s2073_zero : CertifiedContract :=
  ⟨2073, 2076, 0, .none, s2073_zero_contract, 411, s2073_zero_checked⟩

def s2073_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2073_positive_checked : check 414 s2073_positive_contract = true := by decide +kernel
def s2073_positive : CertifiedContract :=
  ⟨2073, 2074, 1, (.dec 8), s2073_positive_contract, 414, s2073_positive_checked⟩

def s2074_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2074_plain_checked : check 409 s2074_plain_contract = true := by decide +kernel
def s2074_plain : CertifiedContract :=
  ⟨2074, 2075, 0, (.inc 2), s2074_plain_contract, 409, s2074_plain_checked⟩

def s2075_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2075_plain_checked : check 113 s2075_plain_contract = true := by decide +kernel
def s2075_plain : CertifiedContract :=
  ⟨2075, 2073, 0, .none, s2075_plain_contract, 113, s2075_plain_checked⟩

def s2076_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2076_plain_checked : check 116 s2076_plain_contract = true := by decide +kernel
def s2076_plain : CertifiedContract :=
  ⟨2076, 2067, 0, .none, s2076_plain_contract, 116, s2076_plain_checked⟩

def s2077_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s2077_zero_checked : check 381 s2077_zero_contract = true := by decide +kernel
def s2077_zero : CertifiedContract :=
  ⟨2077, 2080, 0, .none, s2077_zero_contract, 381, s2077_zero_checked⟩

def s2077_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2077_positive_checked : check 378 s2077_positive_contract = true := by decide +kernel
def s2077_positive : CertifiedContract :=
  ⟨2077, 2078, 1, (.dec 5), s2077_positive_contract, 378, s2077_positive_checked⟩

def s2078_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2078_plain_checked : check 391 s2078_plain_contract = true := by decide +kernel
def s2078_plain : CertifiedContract :=
  ⟨2078, 2079, 0, (.inc 0), s2078_plain_contract, 391, s2078_plain_checked⟩

def s2079_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s2079_plain_checked : check 104 s2079_plain_contract = true := by decide +kernel
def s2079_plain : CertifiedContract :=
  ⟨2079, 2077, 0, .none, s2079_plain_contract, 104, s2079_plain_checked⟩

def s2080_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s2080_zero_checked : check 345 s2080_zero_contract = true := by decide +kernel
def s2080_zero : CertifiedContract :=
  ⟨2080, 2084, 0, .none, s2080_zero_contract, 345, s2080_zero_checked⟩

def s2080_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 1 (.dec 3)⟩
theorem s2080_positive_checked : check 351 s2080_positive_contract = true := by decide +kernel
def s2080_positive : CertifiedContract :=
  ⟨2080, 2081, 1, (.dec 3), s2080_positive_contract, 351, s2080_positive_checked⟩

def s2081_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2081_plain_checked : check 364 s2081_plain_contract = true := by decide +kernel
def s2081_plain : CertifiedContract :=
  ⟨2081, 2082, 0, (.inc 2), s2081_plain_contract, 364, s2081_plain_checked⟩

def s2082_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2082_plain_checked : check 391 s2082_plain_contract = true := by decide +kernel
def s2082_plain : CertifiedContract :=
  ⟨2082, 2083, 0, (.inc 8), s2082_plain_contract, 391, s2082_plain_checked⟩

def s2083_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s2083_plain_checked : check 104 s2083_plain_contract = true := by decide +kernel
def s2083_plain : CertifiedContract :=
  ⟨2083, 2080, 0, .none, s2083_plain_contract, 104, s2083_plain_checked⟩

def s2084_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s2084_zero_checked : check 354 s2084_zero_contract = true := by decide +kernel
def s2084_zero : CertifiedContract :=
  ⟨2084, 2087, 0, .none, s2084_zero_contract, 354, s2084_zero_checked⟩

def s2084_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2084_positive_checked : check 351 s2084_positive_contract = true := by decide +kernel
def s2084_positive : CertifiedContract :=
  ⟨2084, 2085, 1, (.dec 8), s2084_positive_contract, 351, s2084_positive_checked⟩

def s2085_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, true, true, true] 0 (.inc 3)⟩
theorem s2085_plain_checked : check 367 s2085_plain_contract = true := by decide +kernel
def s2085_plain : CertifiedContract :=
  ⟨2085, 2086, 0, (.inc 3), s2085_plain_contract, 367, s2085_plain_checked⟩

def s2086_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s2086_plain_checked : check 95 s2086_plain_contract = true := by decide +kernel
def s2086_plain : CertifiedContract :=
  ⟨2086, 2084, 0, .none, s2086_plain_contract, 95, s2086_plain_checked⟩

def s2087_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s2087_zero_checked : check 336 s2087_zero_contract = true := by decide +kernel
def s2087_zero : CertifiedContract :=
  ⟨2087, 2090, 0, .none, s2087_zero_contract, 336, s2087_zero_checked⟩

def s2087_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2087_positive_checked : check 342 s2087_positive_contract = true := by decide +kernel
def s2087_positive : CertifiedContract :=
  ⟨2087, 2088, 1, (.dec 2), s2087_positive_contract, 342, s2087_positive_checked⟩

def s2088_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2088_plain_checked : check 355 s2088_plain_contract = true := by decide +kernel
def s2088_plain : CertifiedContract :=
  ⟨2088, 2089, 0, (.inc 8), s2088_plain_contract, 355, s2088_plain_checked⟩

def s2089_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s2089_plain_checked : check 92 s2089_plain_contract = true := by decide +kernel
def s2089_plain : CertifiedContract :=
  ⟨2089, 2087, 0, .none, s2089_plain_contract, 92, s2089_plain_checked⟩

def s2090_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2090_zero_checked : check 357 s2090_zero_contract = true := by decide +kernel
def s2090_zero : CertifiedContract :=
  ⟨2090, 2093, 0, .none, s2090_zero_contract, 357, s2090_zero_checked⟩

def s2090_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2090_positive_checked : check 363 s2090_positive_contract = true := by decide +kernel
def s2090_positive : CertifiedContract :=
  ⟨2090, 2091, 1, (.dec 0), s2090_positive_contract, 363, s2090_positive_checked⟩

def s2091_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2091_plain_checked : check 355 s2091_plain_contract = true := by decide +kernel
def s2091_plain : CertifiedContract :=
  ⟨2091, 2092, 0, (.inc 2), s2091_plain_contract, 355, s2091_plain_checked⟩

def s2092_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s2092_plain_checked : check 95 s2092_plain_contract = true := by decide +kernel
def s2092_plain : CertifiedContract :=
  ⟨2092, 2090, 0, .none, s2092_plain_contract, 95, s2092_plain_checked⟩

def s2093_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2093_zero_checked : check 363 s2093_zero_contract = true := by decide +kernel
def s2093_zero : CertifiedContract :=
  ⟨2093, 2097, 0, .none, s2093_zero_contract, 363, s2093_zero_checked⟩

def s2093_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2093_positive_checked : check 369 s2093_positive_contract = true := by decide +kernel
def s2093_positive : CertifiedContract :=
  ⟨2093, 2094, 1, (.dec 2), s2093_positive_contract, 369, s2093_positive_checked⟩

def s2094_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2094_plain_checked : check 382 s2094_plain_contract = true := by decide +kernel
def s2094_plain : CertifiedContract :=
  ⟨2094, 2095, 0, (.inc 5), s2094_plain_contract, 382, s2094_plain_checked⟩

def s2095_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2095_plain_checked : check 409 s2095_plain_contract = true := by decide +kernel
def s2095_plain : CertifiedContract :=
  ⟨2095, 2096, 0, (.inc 8), s2095_plain_contract, 409, s2095_plain_checked⟩

def s2096_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2096_plain_checked : check 110 s2096_plain_contract = true := by decide +kernel
def s2096_plain : CertifiedContract :=
  ⟨2096, 2093, 0, .none, s2096_plain_contract, 110, s2096_plain_checked⟩

def s2097_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2097_zero_checked : check 384 s2097_zero_contract = true := by decide +kernel
def s2097_zero : CertifiedContract :=
  ⟨2097, 2103, 0, .none, s2097_zero_contract, 384, s2097_zero_checked⟩

def s2097_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2097_positive_checked : check 387 s2097_positive_contract = true := by decide +kernel
def s2097_positive : CertifiedContract :=
  ⟨2097, 2098, 1, (.dec 8), s2097_positive_contract, 387, s2097_positive_checked⟩

def s2098_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2098_plain_checked : check 382 s2098_plain_contract = true := by decide +kernel
def s2098_plain : CertifiedContract :=
  ⟨2098, 2099, 0, (.inc 5), s2098_plain_contract, 382, s2098_plain_checked⟩

def s2099_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2099_zero_checked : check 402 s2099_zero_contract = true := by decide +kernel
def s2099_zero : CertifiedContract :=
  ⟨2099, 2102, 0, .none, s2099_zero_contract, 402, s2099_zero_checked⟩

def s2099_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2099_positive_checked : check 405 s2099_positive_contract = true := by decide +kernel
def s2099_positive : CertifiedContract :=
  ⟨2099, 2100, 1, (.dec 8), s2099_positive_contract, 405, s2099_positive_checked⟩

def s2100_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2100_plain_checked : check 400 s2100_plain_contract = true := by decide +kernel
def s2100_plain : CertifiedContract :=
  ⟨2100, 2101, 0, (.inc 2), s2100_plain_contract, 400, s2100_plain_checked⟩

def s2101_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2101_plain_checked : check 110 s2101_plain_contract = true := by decide +kernel
def s2101_plain : CertifiedContract :=
  ⟨2101, 2099, 0, .none, s2101_plain_contract, 110, s2101_plain_checked⟩

def s2102_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2102_plain_checked : check 113 s2102_plain_contract = true := by decide +kernel
def s2102_plain : CertifiedContract :=
  ⟨2102, 2093, 0, .none, s2102_plain_contract, 113, s2102_plain_checked⟩

def s2103_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, false, false] 0 .none⟩
theorem s2103_zero_checked : check 372 s2103_zero_contract = true := by decide +kernel
def s2103_zero : CertifiedContract :=
  ⟨2103, 2106, 0, .none, s2103_zero_contract, 372, s2103_zero_checked⟩

def s2103_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2103_positive_checked : check 369 s2103_positive_contract = true := by decide +kernel
def s2103_positive : CertifiedContract :=
  ⟨2103, 2104, 1, (.dec 5), s2103_positive_contract, 369, s2103_positive_checked⟩

def s2104_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2104_plain_checked : check 382 s2104_plain_contract = true := by decide +kernel
def s2104_plain : CertifiedContract :=
  ⟨2104, 2105, 0, (.inc 0), s2104_plain_contract, 382, s2104_plain_checked⟩

def s2105_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2105_plain_checked : check 101 s2105_plain_contract = true := by decide +kernel
def s2105_plain : CertifiedContract :=
  ⟨2105, 2103, 0, .none, s2105_plain_contract, 101, s2105_plain_checked⟩

def s2106_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s2106_zero_checked : check 336 s2106_zero_contract = true := by decide +kernel
def s2106_zero : CertifiedContract :=
  ⟨2106, 2110, 0, .none, s2106_zero_contract, 336, s2106_zero_checked⟩

def s2106_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, false, true, false] 1 (.dec 7)⟩
theorem s2106_positive_checked : check 342 s2106_positive_contract = true := by decide +kernel
def s2106_positive : CertifiedContract :=
  ⟨2106, 2107, 1, (.dec 7), s2106_positive_contract, 342, s2106_positive_checked⟩

def s2107_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2107_plain_checked : check 346 s2107_plain_contract = true := by decide +kernel
def s2107_plain : CertifiedContract :=
  ⟨2107, 2108, 0, (.inc 2), s2107_plain_contract, 346, s2107_plain_checked⟩

def s2108_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2108_plain_checked : check 373 s2108_plain_contract = true := by decide +kernel
def s2108_plain : CertifiedContract :=
  ⟨2108, 2109, 0, (.inc 8), s2108_plain_contract, 373, s2108_plain_checked⟩

def s2109_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, false, false] 0 .none⟩
theorem s2109_plain_checked : check 98 s2109_plain_contract = true := by decide +kernel
def s2109_plain : CertifiedContract :=
  ⟨2109, 2106, 0, .none, s2109_plain_contract, 98, s2109_plain_checked⟩

def s2110_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s2110_zero_checked : check 342 s2110_zero_contract = true := by decide +kernel
def s2110_zero : CertifiedContract :=
  ⟨2110, 2113, 0, .none, s2110_zero_contract, 342, s2110_zero_checked⟩

def s2110_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, true, true, false] 1 (.dec 8)⟩
theorem s2110_positive_checked : check 342 s2110_positive_contract = true := by decide +kernel
def s2110_positive : CertifiedContract :=
  ⟨2110, 2111, 1, (.dec 8), s2110_positive_contract, 342, s2110_positive_checked⟩

def s2111_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, true, true, true] 0 (.inc 7)⟩
theorem s2111_plain_checked : check 373 s2111_plain_contract = true := by decide +kernel
def s2111_plain : CertifiedContract :=
  ⟨2111, 2112, 0, (.inc 7), s2111_plain_contract, 373, s2111_plain_checked⟩

def s2112_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s2112_plain_checked : check 92 s2112_plain_contract = true := by decide +kernel
def s2112_plain : CertifiedContract :=
  ⟨2112, 2110, 0, .none, s2112_plain_contract, 92, s2112_plain_checked⟩

def s2113_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s2113_zero_checked : check 336 s2113_zero_contract = true := by decide +kernel
def s2113_zero : CertifiedContract :=
  ⟨2113, 2116, 0, .none, s2113_zero_contract, 336, s2113_zero_checked⟩

def s2113_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2113_positive_checked : check 342 s2113_positive_contract = true := by decide +kernel
def s2113_positive : CertifiedContract :=
  ⟨2113, 2114, 1, (.dec 2), s2113_positive_contract, 342, s2113_positive_checked⟩

def s2114_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2114_plain_checked : check 355 s2114_plain_contract = true := by decide +kernel
def s2114_plain : CertifiedContract :=
  ⟨2114, 2115, 0, (.inc 8), s2114_plain_contract, 355, s2114_plain_checked⟩

def s2115_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s2115_plain_checked : check 92 s2115_plain_contract = true := by decide +kernel
def s2115_plain : CertifiedContract :=
  ⟨2115, 2113, 0, .none, s2115_plain_contract, 92, s2115_plain_checked⟩

def s2116_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s2116_zero_checked : check 357 s2116_zero_contract = true := by decide +kernel
def s2116_zero : CertifiedContract :=
  ⟨2116, 2119, 0, .none, s2116_zero_contract, 357, s2116_zero_checked⟩

def s2116_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2116_positive_checked : check 363 s2116_positive_contract = true := by decide +kernel
def s2116_positive : CertifiedContract :=
  ⟨2116, 2117, 1, (.dec 0), s2116_positive_contract, 363, s2116_positive_checked⟩

def s2117_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2117_plain_checked : check 355 s2117_plain_contract = true := by decide +kernel
def s2117_plain : CertifiedContract :=
  ⟨2117, 2118, 0, (.inc 2), s2117_plain_contract, 355, s2117_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S042
