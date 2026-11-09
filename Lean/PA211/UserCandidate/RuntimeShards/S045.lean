import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S045
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2217_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s2217_plain_checked : check 107 s2217_plain_contract = true := by decide +kernel
def s2217_plain : CertifiedContract :=
  ⟨2217, 2214, 0, .none, s2217_plain_contract, 107, s2217_plain_checked⟩

def s2218_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2218_zero_checked : check 360 s2218_zero_contract = true := by decide +kernel
def s2218_zero : CertifiedContract :=
  ⟨2218, 2221, 0, .none, s2218_zero_contract, 360, s2218_zero_checked⟩

def s2218_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s2218_positive_checked : check 360 s2218_positive_contract = true := by decide +kernel
def s2218_positive : CertifiedContract :=
  ⟨2218, 2219, 1, (.dec 8), s2218_positive_contract, 360, s2218_positive_checked⟩

def s2219_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s2219_plain_checked : check 376 s2219_plain_contract = true := by decide +kernel
def s2219_plain : CertifiedContract :=
  ⟨2219, 2220, 0, (.inc 3), s2219_plain_contract, 376, s2219_plain_checked⟩

def s2220_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2220_plain_checked : check 98 s2220_plain_contract = true := by decide +kernel
def s2220_plain : CertifiedContract :=
  ⟨2220, 2218, 0, .none, s2220_plain_contract, 98, s2220_plain_checked⟩

def s2221_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2221_zero_checked : check 354 s2221_zero_contract = true := by decide +kernel
def s2221_zero : CertifiedContract :=
  ⟨2221, 2224, 0, .none, s2221_zero_contract, 354, s2221_zero_checked⟩

def s2221_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2221_positive_checked : check 360 s2221_positive_contract = true := by decide +kernel
def s2221_positive : CertifiedContract :=
  ⟨2221, 2222, 1, (.dec 2), s2221_positive_contract, 360, s2221_positive_checked⟩

def s2222_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2222_plain_checked : check 373 s2222_plain_contract = true := by decide +kernel
def s2222_plain : CertifiedContract :=
  ⟨2222, 2223, 0, (.inc 8), s2222_plain_contract, 373, s2222_plain_checked⟩

def s2223_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2223_plain_checked : check 98 s2223_plain_contract = true := by decide +kernel
def s2223_plain : CertifiedContract :=
  ⟨2223, 2221, 0, .none, s2223_plain_contract, 98, s2223_plain_checked⟩

def s2224_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2224_zero_checked : check 375 s2224_zero_contract = true := by decide +kernel
def s2224_zero : CertifiedContract :=
  ⟨2224, 2227, 0, .none, s2224_zero_contract, 375, s2224_zero_checked⟩

def s2224_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2224_positive_checked : check 381 s2224_positive_contract = true := by decide +kernel
def s2224_positive : CertifiedContract :=
  ⟨2224, 2225, 1, (.dec 0), s2224_positive_contract, 381, s2224_positive_checked⟩

def s2225_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2225_plain_checked : check 373 s2225_plain_contract = true := by decide +kernel
def s2225_plain : CertifiedContract :=
  ⟨2225, 2226, 0, (.inc 2), s2225_plain_contract, 373, s2225_plain_checked⟩

def s2226_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2226_plain_checked : check 101 s2226_plain_contract = true := by decide +kernel
def s2226_plain : CertifiedContract :=
  ⟨2226, 2224, 0, .none, s2226_plain_contract, 101, s2226_plain_checked⟩

def s2227_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2227_zero_checked : check 381 s2227_zero_contract = true := by decide +kernel
def s2227_zero : CertifiedContract :=
  ⟨2227, 2231, 0, .none, s2227_zero_contract, 381, s2227_zero_checked⟩

def s2227_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2227_positive_checked : check 387 s2227_positive_contract = true := by decide +kernel
def s2227_positive : CertifiedContract :=
  ⟨2227, 2228, 1, (.dec 2), s2227_positive_contract, 387, s2227_positive_checked⟩

def s2228_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2228_plain_checked : check 400 s2228_plain_contract = true := by decide +kernel
def s2228_plain : CertifiedContract :=
  ⟨2228, 2229, 0, (.inc 5), s2228_plain_contract, 400, s2228_plain_checked⟩

def s2229_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2229_plain_checked : check 427 s2229_plain_contract = true := by decide +kernel
def s2229_plain : CertifiedContract :=
  ⟨2229, 2230, 0, (.inc 8), s2229_plain_contract, 427, s2229_plain_checked⟩

def s2230_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2230_plain_checked : check 116 s2230_plain_contract = true := by decide +kernel
def s2230_plain : CertifiedContract :=
  ⟨2230, 2227, 0, .none, s2230_plain_contract, 116, s2230_plain_checked⟩

def s2231_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2231_zero_checked : check 402 s2231_zero_contract = true := by decide +kernel
def s2231_zero : CertifiedContract :=
  ⟨2231, 2237, 0, .none, s2231_zero_contract, 402, s2231_zero_checked⟩

def s2231_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2231_positive_checked : check 405 s2231_positive_contract = true := by decide +kernel
def s2231_positive : CertifiedContract :=
  ⟨2231, 2232, 1, (.dec 8), s2231_positive_contract, 405, s2231_positive_checked⟩

def s2232_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2232_plain_checked : check 400 s2232_plain_contract = true := by decide +kernel
def s2232_plain : CertifiedContract :=
  ⟨2232, 2233, 0, (.inc 5), s2232_plain_contract, 400, s2232_plain_checked⟩

def s2233_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2233_zero_checked : check 420 s2233_zero_contract = true := by decide +kernel
def s2233_zero : CertifiedContract :=
  ⟨2233, 2236, 0, .none, s2233_zero_contract, 420, s2233_zero_checked⟩

def s2233_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2233_positive_checked : check 423 s2233_positive_contract = true := by decide +kernel
def s2233_positive : CertifiedContract :=
  ⟨2233, 2234, 1, (.dec 8), s2233_positive_contract, 423, s2233_positive_checked⟩

def s2234_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2234_plain_checked : check 418 s2234_plain_contract = true := by decide +kernel
def s2234_plain : CertifiedContract :=
  ⟨2234, 2235, 0, (.inc 2), s2234_plain_contract, 418, s2234_plain_checked⟩

def s2235_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2235_plain_checked : check 116 s2235_plain_contract = true := by decide +kernel
def s2235_plain : CertifiedContract :=
  ⟨2235, 2233, 0, .none, s2235_plain_contract, 116, s2235_plain_checked⟩

def s2236_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2236_plain_checked : check 119 s2236_plain_contract = true := by decide +kernel
def s2236_plain : CertifiedContract :=
  ⟨2236, 2227, 0, .none, s2236_plain_contract, 119, s2236_plain_checked⟩

def s2237_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s2237_zero_checked : check 390 s2237_zero_contract = true := by decide +kernel
def s2237_zero : CertifiedContract :=
  ⟨2237, 2240, 0, .none, s2237_zero_contract, 390, s2237_zero_checked⟩

def s2237_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2237_positive_checked : check 387 s2237_positive_contract = true := by decide +kernel
def s2237_positive : CertifiedContract :=
  ⟨2237, 2238, 1, (.dec 5), s2237_positive_contract, 387, s2237_positive_checked⟩

def s2238_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2238_plain_checked : check 400 s2238_plain_contract = true := by decide +kernel
def s2238_plain : CertifiedContract :=
  ⟨2238, 2239, 0, (.inc 0), s2238_plain_contract, 400, s2238_plain_checked⟩

def s2239_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2239_plain_checked : check 107 s2239_plain_contract = true := by decide +kernel
def s2239_plain : CertifiedContract :=
  ⟨2239, 2237, 0, .none, s2239_plain_contract, 107, s2239_plain_checked⟩

def s2240_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2240_zero_checked : check 354 s2240_zero_contract = true := by decide +kernel
def s2240_zero : CertifiedContract :=
  ⟨2240, 2244, 0, .none, s2240_zero_contract, 354, s2240_zero_checked⟩

def s2240_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s2240_positive_checked : check 360 s2240_positive_contract = true := by decide +kernel
def s2240_positive : CertifiedContract :=
  ⟨2240, 2241, 1, (.dec 7), s2240_positive_contract, 360, s2240_positive_checked⟩

def s2241_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2241_plain_checked : check 364 s2241_plain_contract = true := by decide +kernel
def s2241_plain : CertifiedContract :=
  ⟨2241, 2242, 0, (.inc 2), s2241_plain_contract, 364, s2241_plain_checked⟩

def s2242_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2242_plain_checked : check 391 s2242_plain_contract = true := by decide +kernel
def s2242_plain : CertifiedContract :=
  ⟨2242, 2243, 0, (.inc 8), s2242_plain_contract, 391, s2242_plain_checked⟩

def s2243_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s2243_plain_checked : check 104 s2243_plain_contract = true := by decide +kernel
def s2243_plain : CertifiedContract :=
  ⟨2243, 2240, 0, .none, s2243_plain_contract, 104, s2243_plain_checked⟩

def s2244_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s2244_zero_checked : check 363 s2244_zero_contract = true := by decide +kernel
def s2244_zero : CertifiedContract :=
  ⟨2244, 2247, 0, .none, s2244_zero_contract, 363, s2244_zero_checked⟩

def s2244_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2244_positive_checked : check 360 s2244_positive_contract = true := by decide +kernel
def s2244_positive : CertifiedContract :=
  ⟨2244, 2245, 1, (.dec 8), s2244_positive_contract, 360, s2244_positive_checked⟩

def s2245_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s2245_plain_checked : check 391 s2245_plain_contract = true := by decide +kernel
def s2245_plain : CertifiedContract :=
  ⟨2245, 2246, 0, (.inc 7), s2245_plain_contract, 391, s2245_plain_checked⟩

def s2246_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2246_plain_checked : check 98 s2246_plain_contract = true := by decide +kernel
def s2246_plain : CertifiedContract :=
  ⟨2246, 2244, 0, .none, s2246_plain_contract, 98, s2246_plain_checked⟩

def s2247_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s2247_zero_checked : check 357 s2247_zero_contract = true := by decide +kernel
def s2247_zero : CertifiedContract :=
  ⟨2247, 2255, 0, .none, s2247_zero_contract, 357, s2247_zero_checked⟩

def s2247_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2247_positive_checked : check 363 s2247_positive_contract = true := by decide +kernel
def s2247_positive : CertifiedContract :=
  ⟨2247, 2248, 1, (.dec 0), s2247_positive_contract, 363, s2247_positive_checked⟩

def s2248_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2248_plain_checked : check 373 s2248_plain_contract = true := by decide +kernel
def s2248_plain : CertifiedContract :=
  ⟨2248, 2249, 0, (.inc 5), s2248_plain_contract, 373, s2248_plain_checked⟩

def s2249_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2249_zero_checked : check 399 s2249_zero_contract = true := by decide +kernel
def s2249_zero : CertifiedContract :=
  ⟨2249, 2251, 0, .none, s2249_zero_contract, 399, s2249_zero_checked⟩

def s2249_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2249_positive_checked : check 405 s2249_positive_contract = true := by decide +kernel
def s2249_positive : CertifiedContract :=
  ⟨2249, 2250, 1, (.dec 8), s2249_positive_contract, 405, s2249_positive_checked⟩

def s2250_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2250_plain_checked : check 110 s2250_plain_contract = true := by decide +kernel
def s2250_plain : CertifiedContract :=
  ⟨2250, 2254, 0, .none, s2250_plain_contract, 110, s2250_plain_checked⟩

def s2251_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2251_zero_checked : check 411 s2251_zero_contract = true := by decide +kernel
def s2251_zero : CertifiedContract :=
  ⟨2251, 2254, 0, .none, s2251_zero_contract, 411, s2251_zero_checked⟩

def s2251_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2251_positive_checked : check 414 s2251_positive_contract = true := by decide +kernel
def s2251_positive : CertifiedContract :=
  ⟨2251, 2252, 1, (.dec 5), s2251_positive_contract, 414, s2251_positive_checked⟩

def s2252_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2252_plain_checked : check 418 s2252_plain_contract = true := by decide +kernel
def s2252_plain : CertifiedContract :=
  ⟨2252, 2253, 0, (.inc 8), s2252_plain_contract, 418, s2252_plain_checked⟩

def s2253_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2253_plain_checked : check 113 s2253_plain_contract = true := by decide +kernel
def s2253_plain : CertifiedContract :=
  ⟨2253, 2251, 0, .none, s2253_plain_contract, 113, s2253_plain_checked⟩

def s2254_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s2254_plain_checked : check 104 s2254_plain_contract = true := by decide +kernel
def s2254_plain : CertifiedContract :=
  ⟨2254, 2247, 0, .none, s2254_plain_contract, 104, s2254_plain_checked⟩

def s2255_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2255_zero_checked : check 357 s2255_zero_contract = true := by decide +kernel
def s2255_zero : CertifiedContract :=
  ⟨2255, 2258, 0, .none, s2255_zero_contract, 357, s2255_zero_checked⟩

def s2255_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2255_positive_checked : check 360 s2255_positive_contract = true := by decide +kernel
def s2255_positive : CertifiedContract :=
  ⟨2255, 2256, 1, (.dec 5), s2255_positive_contract, 360, s2255_positive_checked⟩

def s2256_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2256_plain_checked : check 373 s2256_plain_contract = true := by decide +kernel
def s2256_plain : CertifiedContract :=
  ⟨2256, 2257, 0, (.inc 0), s2256_plain_contract, 373, s2256_plain_checked⟩

def s2257_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s2257_plain_checked : check 98 s2257_plain_contract = true := by decide +kernel
def s2257_plain : CertifiedContract :=
  ⟨2257, 2255, 0, .none, s2257_plain_contract, 98, s2257_plain_checked⟩

def s2258_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s2258_zero_checked : check 354 s2258_zero_contract = true := by decide +kernel
def s2258_zero : CertifiedContract :=
  ⟨2258, 2262, 0, .none, s2258_zero_contract, 354, s2258_zero_checked⟩

def s2258_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2258_positive_checked : check 360 s2258_positive_contract = true := by decide +kernel
def s2258_positive : CertifiedContract :=
  ⟨2258, 2259, 1, (.dec 2), s2258_positive_contract, 360, s2258_positive_checked⟩

def s2259_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2259_plain_checked : check 373 s2259_plain_contract = true := by decide +kernel
def s2259_plain : CertifiedContract :=
  ⟨2259, 2260, 0, (.inc 5), s2259_plain_contract, 373, s2259_plain_checked⟩

def s2260_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2260_plain_checked : check 400 s2260_plain_contract = true := by decide +kernel
def s2260_plain : CertifiedContract :=
  ⟨2260, 2261, 0, (.inc 8), s2260_plain_contract, 400, s2260_plain_checked⟩

def s2261_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2261_plain_checked : check 107 s2261_plain_contract = true := by decide +kernel
def s2261_plain : CertifiedContract :=
  ⟨2261, 2258, 0, .none, s2261_plain_contract, 107, s2261_plain_checked⟩

def s2262_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s2262_zero_checked : check 375 s2262_zero_contract = true := by decide +kernel
def s2262_zero : CertifiedContract :=
  ⟨2262, 2268, 0, .none, s2262_zero_contract, 375, s2262_zero_checked⟩

def s2262_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2262_positive_checked : check 378 s2262_positive_contract = true := by decide +kernel
def s2262_positive : CertifiedContract :=
  ⟨2262, 2263, 1, (.dec 8), s2262_positive_contract, 378, s2262_positive_checked⟩

def s2263_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2263_plain_checked : check 373 s2263_plain_contract = true := by decide +kernel
def s2263_plain : CertifiedContract :=
  ⟨2263, 2264, 0, (.inc 5), s2263_plain_contract, 373, s2263_plain_checked⟩

def s2264_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s2264_zero_checked : check 393 s2264_zero_contract = true := by decide +kernel
def s2264_zero : CertifiedContract :=
  ⟨2264, 2267, 0, .none, s2264_zero_contract, 393, s2264_zero_checked⟩

def s2264_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2264_positive_checked : check 396 s2264_positive_contract = true := by decide +kernel
def s2264_positive : CertifiedContract :=
  ⟨2264, 2265, 1, (.dec 8), s2264_positive_contract, 396, s2264_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S045
