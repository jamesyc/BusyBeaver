module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S043
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2118_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s2118_plain_checked : check 95 s2118_plain_contract = true := by decide +kernel
def s2118_plain : CertifiedContract :=
  ⟨2118, 2116, 0, .none, s2118_plain_contract, 95, s2118_plain_checked⟩

def s2119_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2119_zero_checked : check 363 s2119_zero_contract = true := by decide +kernel
def s2119_zero : CertifiedContract :=
  ⟨2119, 2123, 0, .none, s2119_zero_contract, 363, s2119_zero_checked⟩

def s2119_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2119_positive_checked : check 369 s2119_positive_contract = true := by decide +kernel
def s2119_positive : CertifiedContract :=
  ⟨2119, 2120, 1, (.dec 2), s2119_positive_contract, 369, s2119_positive_checked⟩

def s2120_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2120_plain_checked : check 382 s2120_plain_contract = true := by decide +kernel
def s2120_plain : CertifiedContract :=
  ⟨2120, 2121, 0, (.inc 5), s2120_plain_contract, 382, s2120_plain_checked⟩

def s2121_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2121_plain_checked : check 409 s2121_plain_contract = true := by decide +kernel
def s2121_plain : CertifiedContract :=
  ⟨2121, 2122, 0, (.inc 8), s2121_plain_contract, 409, s2121_plain_checked⟩

def s2122_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s2122_plain_checked : check 110 s2122_plain_contract = true := by decide +kernel
def s2122_plain : CertifiedContract :=
  ⟨2122, 2119, 0, .none, s2122_plain_contract, 110, s2122_plain_checked⟩

def s2123_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s2123_zero_checked : check 384 s2123_zero_contract = true := by decide +kernel
def s2123_zero : CertifiedContract :=
  ⟨2123, 2129, 0, .none, s2123_zero_contract, 384, s2123_zero_checked⟩

def s2123_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2123_positive_checked : check 387 s2123_positive_contract = true := by decide +kernel
def s2123_positive : CertifiedContract :=
  ⟨2123, 2124, 1, (.dec 8), s2123_positive_contract, 387, s2123_positive_checked⟩

def s2124_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2124_plain_checked : check 382 s2124_plain_contract = true := by decide +kernel
def s2124_plain : CertifiedContract :=
  ⟨2124, 2125, 0, (.inc 5), s2124_plain_contract, 382, s2124_plain_checked⟩

def s2125_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2125_zero_checked : check 402 s2125_zero_contract = true := by decide +kernel
def s2125_zero : CertifiedContract :=
  ⟨2125, 2128, 0, .none, s2125_zero_contract, 402, s2125_zero_checked⟩

def s2125_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2125_positive_checked : check 405 s2125_positive_contract = true := by decide +kernel
def s2125_positive : CertifiedContract :=
  ⟨2125, 2126, 1, (.dec 8), s2125_positive_contract, 405, s2125_positive_checked⟩

def s2126_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2126_plain_checked : check 400 s2126_plain_contract = true := by decide +kernel
def s2126_plain : CertifiedContract :=
  ⟨2126, 2127, 0, (.inc 2), s2126_plain_contract, 400, s2126_plain_checked⟩

def s2127_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2127_plain_checked : check 110 s2127_plain_contract = true := by decide +kernel
def s2127_plain : CertifiedContract :=
  ⟨2127, 2125, 0, .none, s2127_plain_contract, 110, s2127_plain_checked⟩

def s2128_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s2128_plain_checked : check 113 s2128_plain_contract = true := by decide +kernel
def s2128_plain : CertifiedContract :=
  ⟨2128, 2119, 0, .none, s2128_plain_contract, 113, s2128_plain_checked⟩

def s2129_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, false] 0 .none⟩
theorem s2129_zero_checked : check 372 s2129_zero_contract = true := by decide +kernel
def s2129_zero : CertifiedContract :=
  ⟨2129, 2132, 0, .none, s2129_zero_contract, 372, s2129_zero_checked⟩

def s2129_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2129_positive_checked : check 369 s2129_positive_contract = true := by decide +kernel
def s2129_positive : CertifiedContract :=
  ⟨2129, 2130, 1, (.dec 5), s2129_positive_contract, 369, s2129_positive_checked⟩

def s2130_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2130_plain_checked : check 382 s2130_plain_contract = true := by decide +kernel
def s2130_plain : CertifiedContract :=
  ⟨2130, 2131, 0, (.inc 0), s2130_plain_contract, 382, s2130_plain_checked⟩

def s2131_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s2131_plain_checked : check 101 s2131_plain_contract = true := by decide +kernel
def s2131_plain : CertifiedContract :=
  ⟨2131, 2129, 0, .none, s2131_plain_contract, 101, s2131_plain_checked⟩

def s2132_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s2132_zero_checked : check 336 s2132_zero_contract = true := by decide +kernel
def s2132_zero : CertifiedContract :=
  ⟨2132, 2136, 0, .none, s2132_zero_contract, 336, s2132_zero_checked⟩

def s2132_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, false] 1 (.dec 4)⟩
theorem s2132_positive_checked : check 342 s2132_positive_contract = true := by decide +kernel
def s2132_positive : CertifiedContract :=
  ⟨2132, 2133, 1, (.dec 4), s2132_positive_contract, 342, s2132_positive_checked⟩

def s2133_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2133_plain_checked : check 355 s2133_plain_contract = true := by decide +kernel
def s2133_plain : CertifiedContract :=
  ⟨2133, 2134, 0, (.inc 2), s2133_plain_contract, 355, s2133_plain_checked⟩

def s2134_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2134_plain_checked : check 382 s2134_plain_contract = true := by decide +kernel
def s2134_plain : CertifiedContract :=
  ⟨2134, 2135, 0, (.inc 8), s2134_plain_contract, 382, s2134_plain_checked⟩

def s2135_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, false] 0 .none⟩
theorem s2135_plain_checked : check 101 s2135_plain_contract = true := by decide +kernel
def s2135_plain : CertifiedContract :=
  ⟨2135, 2132, 0, .none, s2135_plain_contract, 101, s2135_plain_checked⟩

def s2136_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, false] 0 .none⟩
theorem s2136_zero_checked : check 354 s2136_zero_contract = true := by decide +kernel
def s2136_zero : CertifiedContract :=
  ⟨2136, 2139, 0, .none, s2136_zero_contract, 354, s2136_zero_checked⟩

def s2136_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2136_positive_checked : check 342 s2136_positive_contract = true := by decide +kernel
def s2136_positive : CertifiedContract :=
  ⟨2136, 2137, 1, (.dec 8), s2136_positive_contract, 342, s2136_positive_checked⟩

def s2137_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true] 0 (.inc 4)⟩
theorem s2137_plain_checked : check 346 s2137_plain_contract = true := by decide +kernel
def s2137_plain : CertifiedContract :=
  ⟨2137, 2138, 0, (.inc 4), s2137_plain_contract, 346, s2137_plain_checked⟩

def s2138_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s2138_plain_checked : check 92 s2138_plain_contract = true := by decide +kernel
def s2138_plain : CertifiedContract :=
  ⟨2138, 2136, 0, .none, s2138_plain_contract, 92, s2138_plain_checked⟩

def s2139_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, false] 0 .none⟩
theorem s2139_zero_checked : check 339 s2139_zero_contract = true := by decide +kernel
def s2139_zero : CertifiedContract :=
  ⟨2139, 2147, 0, .none, s2139_zero_contract, 339, s2139_zero_checked⟩

def s2139_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2139_positive_checked : check 345 s2139_positive_contract = true := by decide +kernel
def s2139_positive : CertifiedContract :=
  ⟨2139, 2140, 1, (.dec 0), s2139_positive_contract, 345, s2139_positive_checked⟩

def s2140_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2140_plain_checked : check 355 s2140_plain_contract = true := by decide +kernel
def s2140_plain : CertifiedContract :=
  ⟨2140, 2141, 0, (.inc 5), s2140_plain_contract, 355, s2140_plain_checked⟩

def s2141_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2141_zero_checked : check 381 s2141_zero_contract = true := by decide +kernel
def s2141_zero : CertifiedContract :=
  ⟨2141, 2143, 0, .none, s2141_zero_contract, 381, s2141_zero_checked⟩

def s2141_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2141_positive_checked : check 387 s2141_positive_contract = true := by decide +kernel
def s2141_positive : CertifiedContract :=
  ⟨2141, 2142, 1, (.dec 8), s2141_positive_contract, 387, s2141_positive_checked⟩

def s2142_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s2142_plain_checked : check 104 s2142_plain_contract = true := by decide +kernel
def s2142_plain : CertifiedContract :=
  ⟨2142, 2146, 0, .none, s2142_plain_contract, 104, s2142_plain_checked⟩

def s2143_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s2143_zero_checked : check 393 s2143_zero_contract = true := by decide +kernel
def s2143_zero : CertifiedContract :=
  ⟨2143, 2146, 0, .none, s2143_zero_contract, 393, s2143_zero_checked⟩

def s2143_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2143_positive_checked : check 396 s2143_positive_contract = true := by decide +kernel
def s2143_positive : CertifiedContract :=
  ⟨2143, 2144, 1, (.dec 5), s2143_positive_contract, 396, s2143_positive_checked⟩

def s2144_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2144_plain_checked : check 400 s2144_plain_contract = true := by decide +kernel
def s2144_plain : CertifiedContract :=
  ⟨2144, 2145, 0, (.inc 8), s2144_plain_contract, 400, s2144_plain_checked⟩

def s2145_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2145_plain_checked : check 107 s2145_plain_contract = true := by decide +kernel
def s2145_plain : CertifiedContract :=
  ⟨2145, 2143, 0, .none, s2145_plain_contract, 107, s2145_plain_checked⟩

def s2146_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, false] 0 .none⟩
theorem s2146_plain_checked : check 98 s2146_plain_contract = true := by decide +kernel
def s2146_plain : CertifiedContract :=
  ⟨2146, 2139, 0, .none, s2146_plain_contract, 98, s2146_plain_checked⟩

def s2147_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2147_zero_checked : check 339 s2147_zero_contract = true := by decide +kernel
def s2147_zero : CertifiedContract :=
  ⟨2147, 2150, 0, .none, s2147_zero_contract, 339, s2147_zero_checked⟩

def s2147_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2147_positive_checked : check 342 s2147_positive_contract = true := by decide +kernel
def s2147_positive : CertifiedContract :=
  ⟨2147, 2148, 1, (.dec 5), s2147_positive_contract, 342, s2147_positive_checked⟩

def s2148_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2148_plain_checked : check 355 s2148_plain_contract = true := by decide +kernel
def s2148_plain : CertifiedContract :=
  ⟨2148, 2149, 0, (.inc 0), s2148_plain_contract, 355, s2148_plain_checked⟩

def s2149_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, false] 0 .none⟩
theorem s2149_plain_checked : check 92 s2149_plain_contract = true := by decide +kernel
def s2149_plain : CertifiedContract :=
  ⟨2149, 2147, 0, .none, s2149_plain_contract, 92, s2149_plain_checked⟩

def s2150_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, false] 0 .none⟩
theorem s2150_zero_checked : check 336 s2150_zero_contract = true := by decide +kernel
def s2150_zero : CertifiedContract :=
  ⟨2150, 2154, 0, .none, s2150_zero_contract, 336, s2150_zero_checked⟩

def s2150_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2150_positive_checked : check 342 s2150_positive_contract = true := by decide +kernel
def s2150_positive : CertifiedContract :=
  ⟨2150, 2151, 1, (.dec 2), s2150_positive_contract, 342, s2150_positive_checked⟩

def s2151_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2151_plain_checked : check 355 s2151_plain_contract = true := by decide +kernel
def s2151_plain : CertifiedContract :=
  ⟨2151, 2152, 0, (.inc 5), s2151_plain_contract, 355, s2151_plain_checked⟩

def s2152_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2152_plain_checked : check 382 s2152_plain_contract = true := by decide +kernel
def s2152_plain : CertifiedContract :=
  ⟨2152, 2153, 0, (.inc 8), s2152_plain_contract, 382, s2152_plain_checked⟩

def s2153_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2153_plain_checked : check 101 s2153_plain_contract = true := by decide +kernel
def s2153_plain : CertifiedContract :=
  ⟨2153, 2150, 0, .none, s2153_plain_contract, 101, s2153_plain_checked⟩

def s2154_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false] 0 .none⟩
theorem s2154_zero_checked : check 357 s2154_zero_contract = true := by decide +kernel
def s2154_zero : CertifiedContract :=
  ⟨2154, 2160, 0, .none, s2154_zero_contract, 357, s2154_zero_checked⟩

def s2154_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2154_positive_checked : check 360 s2154_positive_contract = true := by decide +kernel
def s2154_positive : CertifiedContract :=
  ⟨2154, 2155, 1, (.dec 8), s2154_positive_contract, 360, s2154_positive_checked⟩

def s2155_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2155_plain_checked : check 355 s2155_plain_contract = true := by decide +kernel
def s2155_plain : CertifiedContract :=
  ⟨2155, 2156, 0, (.inc 5), s2155_plain_contract, 355, s2155_plain_checked⟩

def s2156_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s2156_zero_checked : check 375 s2156_zero_contract = true := by decide +kernel
def s2156_zero : CertifiedContract :=
  ⟨2156, 2159, 0, .none, s2156_zero_contract, 375, s2156_zero_checked⟩

def s2156_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2156_positive_checked : check 378 s2156_positive_contract = true := by decide +kernel
def s2156_positive : CertifiedContract :=
  ⟨2156, 2157, 1, (.dec 8), s2156_positive_contract, 378, s2156_positive_checked⟩

def s2157_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2157_plain_checked : check 373 s2157_plain_contract = true := by decide +kernel
def s2157_plain : CertifiedContract :=
  ⟨2157, 2158, 0, (.inc 2), s2157_plain_contract, 373, s2157_plain_checked⟩

def s2158_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2158_plain_checked : check 101 s2158_plain_contract = true := by decide +kernel
def s2158_plain : CertifiedContract :=
  ⟨2158, 2156, 0, .none, s2158_plain_contract, 101, s2158_plain_checked⟩

def s2159_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2159_plain_checked : check 104 s2159_plain_contract = true := by decide +kernel
def s2159_plain : CertifiedContract :=
  ⟨2159, 2150, 0, .none, s2159_plain_contract, 104, s2159_plain_checked⟩

def s2160_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s2160_zero_checked : check 342 s2160_zero_contract = true := by decide +kernel
def s2160_zero : CertifiedContract :=
  ⟨2160, 2166, 0, .none, s2160_zero_contract, 342, s2160_zero_checked⟩

def s2160_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2160_positive_checked : check 342 s2160_positive_contract = true := by decide +kernel
def s2160_positive : CertifiedContract :=
  ⟨2160, 2161, 1, (.dec 5), s2160_positive_contract, 342, s2160_positive_checked⟩

def s2161_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2161_plain_checked : check 355 s2161_plain_contract = true := by decide +kernel
def s2161_plain : CertifiedContract :=
  ⟨2161, 2162, 0, (.inc 2), s2161_plain_contract, 355, s2161_plain_checked⟩

def s2162_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2162_plain_checked : check 358 s2162_plain_contract = true := by decide +kernel
def s2162_plain : CertifiedContract :=
  ⟨2162, 2163, 0, (.inc 2), s2162_plain_contract, 358, s2162_plain_checked⟩

def s2163_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2163_plain_checked : check 364 s2163_plain_contract = true := by decide +kernel
def s2163_plain : CertifiedContract :=
  ⟨2163, 2164, 0, (.inc 2), s2163_plain_contract, 364, s2163_plain_checked⟩

def s2164_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2164_plain_checked : check 370 s2164_plain_contract = true := by decide +kernel
def s2164_plain : CertifiedContract :=
  ⟨2164, 2165, 0, (.inc 2), s2164_plain_contract, 370, s2164_plain_checked⟩

def s2165_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false] 0 .none⟩
theorem s2165_plain_checked : check 89 s2165_plain_contract = true := by decide +kernel
def s2165_plain : CertifiedContract :=
  ⟨2165, 2160, 0, .none, s2165_plain_contract, 89, s2165_plain_checked⟩

def s2166_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s2166_zero_checked : check 348 s2166_zero_contract = true := by decide +kernel
def s2166_zero : CertifiedContract :=
  ⟨2166, 2174, 0, .none, s2166_zero_contract, 348, s2166_zero_checked⟩

def s2166_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2166_positive_checked : check 354 s2166_positive_contract = true := by decide +kernel
def s2166_positive : CertifiedContract :=
  ⟨2166, 2167, 1, (.dec 0), s2166_positive_contract, 354, s2166_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S043
