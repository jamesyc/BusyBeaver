import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S043
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2118_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s2118_plain_checked : check 94 s2118_plain_contract = true := by decide +kernel
def s2118_plain : CertifiedContract :=
  ⟨2118, 2116, 0, .none, s2118_plain_contract, 94, s2118_plain_checked⟩

def s2119_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2119_zero_checked : check 362 s2119_zero_contract = true := by decide +kernel
def s2119_zero : CertifiedContract :=
  ⟨2119, 2123, 0, .none, s2119_zero_contract, 362, s2119_zero_checked⟩

def s2119_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2119_positive_checked : check 368 s2119_positive_contract = true := by decide +kernel
def s2119_positive : CertifiedContract :=
  ⟨2119, 2120, 1, (.dec 2), s2119_positive_contract, 368, s2119_positive_checked⟩

def s2120_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2120_plain_checked : check 381 s2120_plain_contract = true := by decide +kernel
def s2120_plain : CertifiedContract :=
  ⟨2120, 2121, 0, (.inc 5), s2120_plain_contract, 381, s2120_plain_checked⟩

def s2121_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2121_plain_checked : check 408 s2121_plain_contract = true := by decide +kernel
def s2121_plain : CertifiedContract :=
  ⟨2121, 2122, 0, (.inc 8), s2121_plain_contract, 408, s2121_plain_checked⟩

def s2122_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s2122_plain_checked : check 109 s2122_plain_contract = true := by decide +kernel
def s2122_plain : CertifiedContract :=
  ⟨2122, 2119, 0, .none, s2122_plain_contract, 109, s2122_plain_checked⟩

def s2123_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s2123_zero_checked : check 383 s2123_zero_contract = true := by decide +kernel
def s2123_zero : CertifiedContract :=
  ⟨2123, 2129, 0, .none, s2123_zero_contract, 383, s2123_zero_checked⟩

def s2123_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2123_positive_checked : check 386 s2123_positive_contract = true := by decide +kernel
def s2123_positive : CertifiedContract :=
  ⟨2123, 2124, 1, (.dec 8), s2123_positive_contract, 386, s2123_positive_checked⟩

def s2124_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2124_plain_checked : check 381 s2124_plain_contract = true := by decide +kernel
def s2124_plain : CertifiedContract :=
  ⟨2124, 2125, 0, (.inc 5), s2124_plain_contract, 381, s2124_plain_checked⟩

def s2125_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2125_zero_checked : check 401 s2125_zero_contract = true := by decide +kernel
def s2125_zero : CertifiedContract :=
  ⟨2125, 2128, 0, .none, s2125_zero_contract, 401, s2125_zero_checked⟩

def s2125_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2125_positive_checked : check 404 s2125_positive_contract = true := by decide +kernel
def s2125_positive : CertifiedContract :=
  ⟨2125, 2126, 1, (.dec 8), s2125_positive_contract, 404, s2125_positive_checked⟩

def s2126_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2126_plain_checked : check 399 s2126_plain_contract = true := by decide +kernel
def s2126_plain : CertifiedContract :=
  ⟨2126, 2127, 0, (.inc 2), s2126_plain_contract, 399, s2126_plain_checked⟩

def s2127_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2127_plain_checked : check 109 s2127_plain_contract = true := by decide +kernel
def s2127_plain : CertifiedContract :=
  ⟨2127, 2125, 0, .none, s2127_plain_contract, 109, s2127_plain_checked⟩

def s2128_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s2128_plain_checked : check 112 s2128_plain_contract = true := by decide +kernel
def s2128_plain : CertifiedContract :=
  ⟨2128, 2119, 0, .none, s2128_plain_contract, 112, s2128_plain_checked⟩

def s2129_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, false] 0 .none⟩
theorem s2129_zero_checked : check 371 s2129_zero_contract = true := by decide +kernel
def s2129_zero : CertifiedContract :=
  ⟨2129, 2132, 0, .none, s2129_zero_contract, 371, s2129_zero_checked⟩

def s2129_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2129_positive_checked : check 368 s2129_positive_contract = true := by decide +kernel
def s2129_positive : CertifiedContract :=
  ⟨2129, 2130, 1, (.dec 5), s2129_positive_contract, 368, s2129_positive_checked⟩

def s2130_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2130_plain_checked : check 381 s2130_plain_contract = true := by decide +kernel
def s2130_plain : CertifiedContract :=
  ⟨2130, 2131, 0, (.inc 0), s2130_plain_contract, 381, s2130_plain_checked⟩

def s2131_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s2131_plain_checked : check 100 s2131_plain_contract = true := by decide +kernel
def s2131_plain : CertifiedContract :=
  ⟨2131, 2129, 0, .none, s2131_plain_contract, 100, s2131_plain_checked⟩

def s2132_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s2132_zero_checked : check 335 s2132_zero_contract = true := by decide +kernel
def s2132_zero : CertifiedContract :=
  ⟨2132, 2136, 0, .none, s2132_zero_contract, 335, s2132_zero_checked⟩

def s2132_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, false] 1 (.dec 4)⟩
theorem s2132_positive_checked : check 341 s2132_positive_contract = true := by decide +kernel
def s2132_positive : CertifiedContract :=
  ⟨2132, 2133, 1, (.dec 4), s2132_positive_contract, 341, s2132_positive_checked⟩

def s2133_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2133_plain_checked : check 354 s2133_plain_contract = true := by decide +kernel
def s2133_plain : CertifiedContract :=
  ⟨2133, 2134, 0, (.inc 2), s2133_plain_contract, 354, s2133_plain_checked⟩

def s2134_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2134_plain_checked : check 381 s2134_plain_contract = true := by decide +kernel
def s2134_plain : CertifiedContract :=
  ⟨2134, 2135, 0, (.inc 8), s2134_plain_contract, 381, s2134_plain_checked⟩

def s2135_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, false] 0 .none⟩
theorem s2135_plain_checked : check 100 s2135_plain_contract = true := by decide +kernel
def s2135_plain : CertifiedContract :=
  ⟨2135, 2132, 0, .none, s2135_plain_contract, 100, s2135_plain_checked⟩

def s2136_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, false] 0 .none⟩
theorem s2136_zero_checked : check 353 s2136_zero_contract = true := by decide +kernel
def s2136_zero : CertifiedContract :=
  ⟨2136, 2139, 0, .none, s2136_zero_contract, 353, s2136_zero_checked⟩

def s2136_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2136_positive_checked : check 341 s2136_positive_contract = true := by decide +kernel
def s2136_positive : CertifiedContract :=
  ⟨2136, 2137, 1, (.dec 8), s2136_positive_contract, 341, s2136_positive_checked⟩

def s2137_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true] 0 (.inc 4)⟩
theorem s2137_plain_checked : check 345 s2137_plain_contract = true := by decide +kernel
def s2137_plain : CertifiedContract :=
  ⟨2137, 2138, 0, (.inc 4), s2137_plain_contract, 345, s2137_plain_checked⟩

def s2138_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s2138_plain_checked : check 91 s2138_plain_contract = true := by decide +kernel
def s2138_plain : CertifiedContract :=
  ⟨2138, 2136, 0, .none, s2138_plain_contract, 91, s2138_plain_checked⟩

def s2139_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, false] 0 .none⟩
theorem s2139_zero_checked : check 338 s2139_zero_contract = true := by decide +kernel
def s2139_zero : CertifiedContract :=
  ⟨2139, 2147, 0, .none, s2139_zero_contract, 338, s2139_zero_checked⟩

def s2139_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2139_positive_checked : check 344 s2139_positive_contract = true := by decide +kernel
def s2139_positive : CertifiedContract :=
  ⟨2139, 2140, 1, (.dec 0), s2139_positive_contract, 344, s2139_positive_checked⟩

def s2140_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2140_plain_checked : check 354 s2140_plain_contract = true := by decide +kernel
def s2140_plain : CertifiedContract :=
  ⟨2140, 2141, 0, (.inc 5), s2140_plain_contract, 354, s2140_plain_checked⟩

def s2141_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2141_zero_checked : check 380 s2141_zero_contract = true := by decide +kernel
def s2141_zero : CertifiedContract :=
  ⟨2141, 2143, 0, .none, s2141_zero_contract, 380, s2141_zero_checked⟩

def s2141_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2141_positive_checked : check 386 s2141_positive_contract = true := by decide +kernel
def s2141_positive : CertifiedContract :=
  ⟨2141, 2142, 1, (.dec 8), s2141_positive_contract, 386, s2141_positive_checked⟩

def s2142_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s2142_plain_checked : check 103 s2142_plain_contract = true := by decide +kernel
def s2142_plain : CertifiedContract :=
  ⟨2142, 2146, 0, .none, s2142_plain_contract, 103, s2142_plain_checked⟩

def s2143_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s2143_zero_checked : check 392 s2143_zero_contract = true := by decide +kernel
def s2143_zero : CertifiedContract :=
  ⟨2143, 2146, 0, .none, s2143_zero_contract, 392, s2143_zero_checked⟩

def s2143_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2143_positive_checked : check 395 s2143_positive_contract = true := by decide +kernel
def s2143_positive : CertifiedContract :=
  ⟨2143, 2144, 1, (.dec 5), s2143_positive_contract, 395, s2143_positive_checked⟩

def s2144_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2144_plain_checked : check 399 s2144_plain_contract = true := by decide +kernel
def s2144_plain : CertifiedContract :=
  ⟨2144, 2145, 0, (.inc 8), s2144_plain_contract, 399, s2144_plain_checked⟩

def s2145_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2145_plain_checked : check 106 s2145_plain_contract = true := by decide +kernel
def s2145_plain : CertifiedContract :=
  ⟨2145, 2143, 0, .none, s2145_plain_contract, 106, s2145_plain_checked⟩

def s2146_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, false] 0 .none⟩
theorem s2146_plain_checked : check 97 s2146_plain_contract = true := by decide +kernel
def s2146_plain : CertifiedContract :=
  ⟨2146, 2139, 0, .none, s2146_plain_contract, 97, s2146_plain_checked⟩

def s2147_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2147_zero_checked : check 338 s2147_zero_contract = true := by decide +kernel
def s2147_zero : CertifiedContract :=
  ⟨2147, 2150, 0, .none, s2147_zero_contract, 338, s2147_zero_checked⟩

def s2147_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2147_positive_checked : check 341 s2147_positive_contract = true := by decide +kernel
def s2147_positive : CertifiedContract :=
  ⟨2147, 2148, 1, (.dec 5), s2147_positive_contract, 341, s2147_positive_checked⟩

def s2148_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2148_plain_checked : check 354 s2148_plain_contract = true := by decide +kernel
def s2148_plain : CertifiedContract :=
  ⟨2148, 2149, 0, (.inc 0), s2148_plain_contract, 354, s2148_plain_checked⟩

def s2149_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, false] 0 .none⟩
theorem s2149_plain_checked : check 91 s2149_plain_contract = true := by decide +kernel
def s2149_plain : CertifiedContract :=
  ⟨2149, 2147, 0, .none, s2149_plain_contract, 91, s2149_plain_checked⟩

def s2150_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, false] 0 .none⟩
theorem s2150_zero_checked : check 335 s2150_zero_contract = true := by decide +kernel
def s2150_zero : CertifiedContract :=
  ⟨2150, 2154, 0, .none, s2150_zero_contract, 335, s2150_zero_checked⟩

def s2150_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2150_positive_checked : check 341 s2150_positive_contract = true := by decide +kernel
def s2150_positive : CertifiedContract :=
  ⟨2150, 2151, 1, (.dec 2), s2150_positive_contract, 341, s2150_positive_checked⟩

def s2151_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2151_plain_checked : check 354 s2151_plain_contract = true := by decide +kernel
def s2151_plain : CertifiedContract :=
  ⟨2151, 2152, 0, (.inc 5), s2151_plain_contract, 354, s2151_plain_checked⟩

def s2152_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2152_plain_checked : check 381 s2152_plain_contract = true := by decide +kernel
def s2152_plain : CertifiedContract :=
  ⟨2152, 2153, 0, (.inc 8), s2152_plain_contract, 381, s2152_plain_checked⟩

def s2153_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2153_plain_checked : check 100 s2153_plain_contract = true := by decide +kernel
def s2153_plain : CertifiedContract :=
  ⟨2153, 2150, 0, .none, s2153_plain_contract, 100, s2153_plain_checked⟩

def s2154_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false] 0 .none⟩
theorem s2154_zero_checked : check 356 s2154_zero_contract = true := by decide +kernel
def s2154_zero : CertifiedContract :=
  ⟨2154, 2160, 0, .none, s2154_zero_contract, 356, s2154_zero_checked⟩

def s2154_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2154_positive_checked : check 359 s2154_positive_contract = true := by decide +kernel
def s2154_positive : CertifiedContract :=
  ⟨2154, 2155, 1, (.dec 8), s2154_positive_contract, 359, s2154_positive_checked⟩

def s2155_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2155_plain_checked : check 354 s2155_plain_contract = true := by decide +kernel
def s2155_plain : CertifiedContract :=
  ⟨2155, 2156, 0, (.inc 5), s2155_plain_contract, 354, s2155_plain_checked⟩

def s2156_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s2156_zero_checked : check 374 s2156_zero_contract = true := by decide +kernel
def s2156_zero : CertifiedContract :=
  ⟨2156, 2159, 0, .none, s2156_zero_contract, 374, s2156_zero_checked⟩

def s2156_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2156_positive_checked : check 377 s2156_positive_contract = true := by decide +kernel
def s2156_positive : CertifiedContract :=
  ⟨2156, 2157, 1, (.dec 8), s2156_positive_contract, 377, s2156_positive_checked⟩

def s2157_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2157_plain_checked : check 372 s2157_plain_contract = true := by decide +kernel
def s2157_plain : CertifiedContract :=
  ⟨2157, 2158, 0, (.inc 2), s2157_plain_contract, 372, s2157_plain_checked⟩

def s2158_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2158_plain_checked : check 100 s2158_plain_contract = true := by decide +kernel
def s2158_plain : CertifiedContract :=
  ⟨2158, 2156, 0, .none, s2158_plain_contract, 100, s2158_plain_checked⟩

def s2159_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2159_plain_checked : check 103 s2159_plain_contract = true := by decide +kernel
def s2159_plain : CertifiedContract :=
  ⟨2159, 2150, 0, .none, s2159_plain_contract, 103, s2159_plain_checked⟩

def s2160_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s2160_zero_checked : check 341 s2160_zero_contract = true := by decide +kernel
def s2160_zero : CertifiedContract :=
  ⟨2160, 2166, 0, .none, s2160_zero_contract, 341, s2160_zero_checked⟩

def s2160_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2160_positive_checked : check 341 s2160_positive_contract = true := by decide +kernel
def s2160_positive : CertifiedContract :=
  ⟨2160, 2161, 1, (.dec 5), s2160_positive_contract, 341, s2160_positive_checked⟩

def s2161_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2161_plain_checked : check 354 s2161_plain_contract = true := by decide +kernel
def s2161_plain : CertifiedContract :=
  ⟨2161, 2162, 0, (.inc 2), s2161_plain_contract, 354, s2161_plain_checked⟩

def s2162_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2162_plain_checked : check 357 s2162_plain_contract = true := by decide +kernel
def s2162_plain : CertifiedContract :=
  ⟨2162, 2163, 0, (.inc 2), s2162_plain_contract, 357, s2162_plain_checked⟩

def s2163_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2163_plain_checked : check 354 s2163_plain_contract = true := by decide +kernel
def s2163_plain : CertifiedContract :=
  ⟨2163, 2164, 0, (.inc 2), s2163_plain_contract, 354, s2163_plain_checked⟩

def s2164_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2164_plain_checked : check 360 s2164_plain_contract = true := by decide +kernel
def s2164_plain : CertifiedContract :=
  ⟨2164, 2165, 0, (.inc 2), s2164_plain_contract, 360, s2164_plain_checked⟩

def s2165_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false] 0 .none⟩
theorem s2165_plain_checked : check 88 s2165_plain_contract = true := by decide +kernel
def s2165_plain : CertifiedContract :=
  ⟨2165, 2160, 0, .none, s2165_plain_contract, 88, s2165_plain_checked⟩

def s2166_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s2166_zero_checked : check 347 s2166_zero_contract = true := by decide +kernel
def s2166_zero : CertifiedContract :=
  ⟨2166, 2174, 0, .none, s2166_zero_contract, 347, s2166_zero_checked⟩

def s2166_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2166_positive_checked : check 353 s2166_positive_contract = true := by decide +kernel
def s2166_positive : CertifiedContract :=
  ⟨2166, 2167, 1, (.dec 0), s2166_positive_contract, 353, s2166_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2118_plain,
  s2119_zero,
  s2119_positive,
  s2120_plain,
  s2121_plain,
  s2122_plain,
  s2123_zero,
  s2123_positive,
  s2124_plain,
  s2125_zero,
  s2125_positive,
  s2126_plain,
  s2127_plain,
  s2128_plain,
  s2129_zero,
  s2129_positive,
  s2130_plain,
  s2131_plain,
  s2132_zero,
  s2132_positive,
  s2133_plain,
  s2134_plain,
  s2135_plain,
  s2136_zero,
  s2136_positive,
  s2137_plain,
  s2138_plain,
  s2139_zero,
  s2139_positive,
  s2140_plain,
  s2141_zero,
  s2141_positive,
  s2142_plain,
  s2143_zero,
  s2143_positive,
  s2144_plain,
  s2145_plain,
  s2146_plain,
  s2147_zero,
  s2147_positive,
  s2148_plain,
  s2149_plain,
  s2150_zero,
  s2150_positive,
  s2151_plain,
  s2152_plain,
  s2153_plain,
  s2154_zero,
  s2154_positive,
  s2155_plain,
  s2156_zero,
  s2156_positive,
  s2157_plain,
  s2158_plain,
  s2159_plain,
  s2160_zero,
  s2160_positive,
  s2161_plain,
  s2162_plain,
  s2163_plain,
  s2164_plain,
  s2165_plain,
  s2166_zero,
  s2166_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S043
