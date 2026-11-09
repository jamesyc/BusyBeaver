module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S044
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2167_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2167_plain_checked : check 364 s2167_plain_contract = true := by decide +kernel
def s2167_plain : CertifiedContract :=
  ⟨2167, 2168, 0, (.inc 5), s2167_plain_contract, 364, s2167_plain_checked⟩

def s2168_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2168_zero_checked : check 390 s2168_zero_contract = true := by decide +kernel
def s2168_zero : CertifiedContract :=
  ⟨2168, 2170, 0, .none, s2168_zero_contract, 390, s2168_zero_checked⟩

def s2168_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2168_positive_checked : check 396 s2168_positive_contract = true := by decide +kernel
def s2168_positive : CertifiedContract :=
  ⟨2168, 2169, 1, (.dec 8), s2168_positive_contract, 396, s2168_positive_checked⟩

def s2169_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2169_plain_checked : check 107 s2169_plain_contract = true := by decide +kernel
def s2169_plain : CertifiedContract :=
  ⟨2169, 2173, 0, .none, s2169_plain_contract, 107, s2169_plain_checked⟩

def s2170_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2170_zero_checked : check 402 s2170_zero_contract = true := by decide +kernel
def s2170_zero : CertifiedContract :=
  ⟨2170, 2173, 0, .none, s2170_zero_contract, 402, s2170_zero_checked⟩

def s2170_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2170_positive_checked : check 405 s2170_positive_contract = true := by decide +kernel
def s2170_positive : CertifiedContract :=
  ⟨2170, 2171, 1, (.dec 5), s2170_positive_contract, 405, s2170_positive_checked⟩

def s2171_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2171_plain_checked : check 409 s2171_plain_contract = true := by decide +kernel
def s2171_plain : CertifiedContract :=
  ⟨2171, 2172, 0, (.inc 8), s2171_plain_contract, 409, s2171_plain_checked⟩

def s2172_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2172_plain_checked : check 110 s2172_plain_contract = true := by decide +kernel
def s2172_plain : CertifiedContract :=
  ⟨2172, 2170, 0, .none, s2172_plain_contract, 110, s2172_plain_checked⟩

def s2173_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s2173_plain_checked : check 101 s2173_plain_contract = true := by decide +kernel
def s2173_plain : CertifiedContract :=
  ⟨2173, 2166, 0, .none, s2173_plain_contract, 101, s2173_plain_checked⟩

def s2174_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2174_zero_checked : check 348 s2174_zero_contract = true := by decide +kernel
def s2174_zero : CertifiedContract :=
  ⟨2174, 2177, 0, .none, s2174_zero_contract, 348, s2174_zero_checked⟩

def s2174_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2174_positive_checked : check 351 s2174_positive_contract = true := by decide +kernel
def s2174_positive : CertifiedContract :=
  ⟨2174, 2175, 1, (.dec 5), s2174_positive_contract, 351, s2174_positive_checked⟩

def s2175_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2175_plain_checked : check 364 s2175_plain_contract = true := by decide +kernel
def s2175_plain : CertifiedContract :=
  ⟨2175, 2176, 0, (.inc 0), s2175_plain_contract, 364, s2175_plain_checked⟩

def s2176_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s2176_plain_checked : check 95 s2176_plain_contract = true := by decide +kernel
def s2176_plain : CertifiedContract :=
  ⟨2176, 2174, 0, .none, s2176_plain_contract, 95, s2176_plain_checked⟩

def s2177_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s2177_zero_checked : check 345 s2177_zero_contract = true := by decide +kernel
def s2177_zero : CertifiedContract :=
  ⟨2177, 2181, 0, .none, s2177_zero_contract, 345, s2177_zero_checked⟩

def s2177_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2177_positive_checked : check 351 s2177_positive_contract = true := by decide +kernel
def s2177_positive : CertifiedContract :=
  ⟨2177, 2178, 1, (.dec 2), s2177_positive_contract, 351, s2177_positive_checked⟩

def s2178_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2178_plain_checked : check 364 s2178_plain_contract = true := by decide +kernel
def s2178_plain : CertifiedContract :=
  ⟨2178, 2179, 0, (.inc 5), s2178_plain_contract, 364, s2178_plain_checked⟩

def s2179_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2179_plain_checked : check 391 s2179_plain_contract = true := by decide +kernel
def s2179_plain : CertifiedContract :=
  ⟨2179, 2180, 0, (.inc 8), s2179_plain_contract, 391, s2179_plain_checked⟩

def s2180_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2180_plain_checked : check 104 s2180_plain_contract = true := by decide +kernel
def s2180_plain : CertifiedContract :=
  ⟨2180, 2177, 0, .none, s2180_plain_contract, 104, s2180_plain_checked⟩

def s2181_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s2181_zero_checked : check 366 s2181_zero_contract = true := by decide +kernel
def s2181_zero : CertifiedContract :=
  ⟨2181, 2187, 0, .none, s2181_zero_contract, 366, s2181_zero_checked⟩

def s2181_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2181_positive_checked : check 369 s2181_positive_contract = true := by decide +kernel
def s2181_positive : CertifiedContract :=
  ⟨2181, 2182, 1, (.dec 8), s2181_positive_contract, 369, s2181_positive_checked⟩

def s2182_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2182_plain_checked : check 364 s2182_plain_contract = true := by decide +kernel
def s2182_plain : CertifiedContract :=
  ⟨2182, 2183, 0, (.inc 5), s2182_plain_contract, 364, s2182_plain_checked⟩

def s2183_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s2183_zero_checked : check 384 s2183_zero_contract = true := by decide +kernel
def s2183_zero : CertifiedContract :=
  ⟨2183, 2186, 0, .none, s2183_zero_contract, 384, s2183_zero_checked⟩

def s2183_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2183_positive_checked : check 387 s2183_positive_contract = true := by decide +kernel
def s2183_positive : CertifiedContract :=
  ⟨2183, 2184, 1, (.dec 8), s2183_positive_contract, 387, s2183_positive_checked⟩

def s2184_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2184_plain_checked : check 382 s2184_plain_contract = true := by decide +kernel
def s2184_plain : CertifiedContract :=
  ⟨2184, 2185, 0, (.inc 2), s2184_plain_contract, 382, s2184_plain_checked⟩

def s2185_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2185_plain_checked : check 104 s2185_plain_contract = true := by decide +kernel
def s2185_plain : CertifiedContract :=
  ⟨2185, 2183, 0, .none, s2185_plain_contract, 104, s2185_plain_checked⟩

def s2186_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2186_plain_checked : check 107 s2186_plain_contract = true := by decide +kernel
def s2186_plain : CertifiedContract :=
  ⟨2186, 2177, 0, .none, s2186_plain_contract, 107, s2186_plain_checked⟩

def s2187_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, true, false] 0 .none⟩
theorem s2187_zero_checked : check 351 s2187_zero_contract = true := by decide +kernel
def s2187_zero : CertifiedContract :=
  ⟨2187, 2193, 0, .none, s2187_zero_contract, 351, s2187_zero_checked⟩

def s2187_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2187_positive_checked : check 351 s2187_positive_contract = true := by decide +kernel
def s2187_positive : CertifiedContract :=
  ⟨2187, 2188, 1, (.dec 5), s2187_positive_contract, 351, s2187_positive_checked⟩

def s2188_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2188_plain_checked : check 364 s2188_plain_contract = true := by decide +kernel
def s2188_plain : CertifiedContract :=
  ⟨2188, 2189, 0, (.inc 2), s2188_plain_contract, 364, s2188_plain_checked⟩

def s2189_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2189_plain_checked : check 367 s2189_plain_contract = true := by decide +kernel
def s2189_plain : CertifiedContract :=
  ⟨2189, 2190, 0, (.inc 2), s2189_plain_contract, 367, s2189_plain_checked⟩

def s2190_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2190_plain_checked : check 373 s2190_plain_contract = true := by decide +kernel
def s2190_plain : CertifiedContract :=
  ⟨2190, 2191, 0, (.inc 2), s2190_plain_contract, 373, s2190_plain_checked⟩

def s2191_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2191_plain_checked : check 379 s2191_plain_contract = true := by decide +kernel
def s2191_plain : CertifiedContract :=
  ⟨2191, 2192, 0, (.inc 2), s2191_plain_contract, 379, s2191_plain_checked⟩

def s2192_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s2192_plain_checked : check 92 s2192_plain_contract = true := by decide +kernel
def s2192_plain : CertifiedContract :=
  ⟨2192, 2187, 0, .none, s2192_plain_contract, 92, s2192_plain_checked⟩

def s2193_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2193_plain_checked : check 319 s2193_plain_contract = true := by decide +kernel
def s2193_plain : CertifiedContract :=
  ⟨2193, 2194, 0, (.inc 2), s2193_plain_contract, 319, s2193_plain_checked⟩

def s2194_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s2194_plain_checked : check 328 s2194_plain_contract = true := by decide +kernel
def s2194_plain : CertifiedContract :=
  ⟨2194, 2195, 0, (.inc 2), s2194_plain_contract, 328, s2194_plain_checked⟩

def s2195_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2195_zero_checked : check 354 s2195_zero_contract = true := by decide +kernel
def s2195_zero : CertifiedContract :=
  ⟨2195, 2198, 0, .none, s2195_zero_contract, 354, s2195_zero_checked⟩

def s2195_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2195_positive_checked : check 360 s2195_positive_contract = true := by decide +kernel
def s2195_positive : CertifiedContract :=
  ⟨2195, 2196, 1, (.dec 2), s2195_positive_contract, 360, s2195_positive_checked⟩

def s2196_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2196_plain_checked : check 373 s2196_plain_contract = true := by decide +kernel
def s2196_plain : CertifiedContract :=
  ⟨2196, 2197, 0, (.inc 8), s2196_plain_contract, 373, s2196_plain_checked⟩

def s2197_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s2197_plain_checked : check 98 s2197_plain_contract = true := by decide +kernel
def s2197_plain : CertifiedContract :=
  ⟨2197, 2195, 0, .none, s2197_plain_contract, 98, s2197_plain_checked⟩

def s2198_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2198_zero_checked : check 375 s2198_zero_contract = true := by decide +kernel
def s2198_zero : CertifiedContract :=
  ⟨2198, 2201, 0, .none, s2198_zero_contract, 375, s2198_zero_checked⟩

def s2198_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2198_positive_checked : check 381 s2198_positive_contract = true := by decide +kernel
def s2198_positive : CertifiedContract :=
  ⟨2198, 2199, 1, (.dec 0), s2198_positive_contract, 381, s2198_positive_checked⟩

def s2199_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2199_plain_checked : check 373 s2199_plain_contract = true := by decide +kernel
def s2199_plain : CertifiedContract :=
  ⟨2199, 2200, 0, (.inc 2), s2199_plain_contract, 373, s2199_plain_checked⟩

def s2200_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2200_plain_checked : check 101 s2200_plain_contract = true := by decide +kernel
def s2200_plain : CertifiedContract :=
  ⟨2200, 2198, 0, .none, s2200_plain_contract, 101, s2200_plain_checked⟩

def s2201_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2201_zero_checked : check 381 s2201_zero_contract = true := by decide +kernel
def s2201_zero : CertifiedContract :=
  ⟨2201, 2205, 0, .none, s2201_zero_contract, 381, s2201_zero_checked⟩

def s2201_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2201_positive_checked : check 387 s2201_positive_contract = true := by decide +kernel
def s2201_positive : CertifiedContract :=
  ⟨2201, 2202, 1, (.dec 2), s2201_positive_contract, 387, s2201_positive_checked⟩

def s2202_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2202_plain_checked : check 400 s2202_plain_contract = true := by decide +kernel
def s2202_plain : CertifiedContract :=
  ⟨2202, 2203, 0, (.inc 5), s2202_plain_contract, 400, s2202_plain_checked⟩

def s2203_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2203_plain_checked : check 427 s2203_plain_contract = true := by decide +kernel
def s2203_plain : CertifiedContract :=
  ⟨2203, 2204, 0, (.inc 8), s2203_plain_contract, 427, s2203_plain_checked⟩

def s2204_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2204_plain_checked : check 116 s2204_plain_contract = true := by decide +kernel
def s2204_plain : CertifiedContract :=
  ⟨2204, 2201, 0, .none, s2204_plain_contract, 116, s2204_plain_checked⟩

def s2205_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2205_zero_checked : check 402 s2205_zero_contract = true := by decide +kernel
def s2205_zero : CertifiedContract :=
  ⟨2205, 2211, 0, .none, s2205_zero_contract, 402, s2205_zero_checked⟩

def s2205_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2205_positive_checked : check 405 s2205_positive_contract = true := by decide +kernel
def s2205_positive : CertifiedContract :=
  ⟨2205, 2206, 1, (.dec 8), s2205_positive_contract, 405, s2205_positive_checked⟩

def s2206_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2206_plain_checked : check 400 s2206_plain_contract = true := by decide +kernel
def s2206_plain : CertifiedContract :=
  ⟨2206, 2207, 0, (.inc 5), s2206_plain_contract, 400, s2206_plain_checked⟩

def s2207_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2207_zero_checked : check 420 s2207_zero_contract = true := by decide +kernel
def s2207_zero : CertifiedContract :=
  ⟨2207, 2210, 0, .none, s2207_zero_contract, 420, s2207_zero_checked⟩

def s2207_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2207_positive_checked : check 423 s2207_positive_contract = true := by decide +kernel
def s2207_positive : CertifiedContract :=
  ⟨2207, 2208, 1, (.dec 8), s2207_positive_contract, 423, s2207_positive_checked⟩

def s2208_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2208_plain_checked : check 418 s2208_plain_contract = true := by decide +kernel
def s2208_plain : CertifiedContract :=
  ⟨2208, 2209, 0, (.inc 2), s2208_plain_contract, 418, s2208_plain_checked⟩

def s2209_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2209_plain_checked : check 116 s2209_plain_contract = true := by decide +kernel
def s2209_plain : CertifiedContract :=
  ⟨2209, 2207, 0, .none, s2209_plain_contract, 116, s2209_plain_checked⟩

def s2210_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2210_plain_checked : check 119 s2210_plain_contract = true := by decide +kernel
def s2210_plain : CertifiedContract :=
  ⟨2210, 2201, 0, .none, s2210_plain_contract, 119, s2210_plain_checked⟩

def s2211_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s2211_zero_checked : check 390 s2211_zero_contract = true := by decide +kernel
def s2211_zero : CertifiedContract :=
  ⟨2211, 2214, 0, .none, s2211_zero_contract, 390, s2211_zero_checked⟩

def s2211_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2211_positive_checked : check 387 s2211_positive_contract = true := by decide +kernel
def s2211_positive : CertifiedContract :=
  ⟨2211, 2212, 1, (.dec 5), s2211_positive_contract, 387, s2211_positive_checked⟩

def s2212_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2212_plain_checked : check 400 s2212_plain_contract = true := by decide +kernel
def s2212_plain : CertifiedContract :=
  ⟨2212, 2213, 0, (.inc 0), s2212_plain_contract, 400, s2212_plain_checked⟩

def s2213_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2213_plain_checked : check 107 s2213_plain_contract = true := by decide +kernel
def s2213_plain : CertifiedContract :=
  ⟨2213, 2211, 0, .none, s2213_plain_contract, 107, s2213_plain_checked⟩

def s2214_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2214_zero_checked : check 354 s2214_zero_contract = true := by decide +kernel
def s2214_zero : CertifiedContract :=
  ⟨2214, 2218, 0, .none, s2214_zero_contract, 354, s2214_zero_checked⟩

def s2214_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s2214_positive_checked : check 360 s2214_positive_contract = true := by decide +kernel
def s2214_positive : CertifiedContract :=
  ⟨2214, 2215, 1, (.dec 3), s2214_positive_contract, 360, s2214_positive_checked⟩

def s2215_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2215_plain_checked : check 373 s2215_plain_contract = true := by decide +kernel
def s2215_plain : CertifiedContract :=
  ⟨2215, 2216, 0, (.inc 2), s2215_plain_contract, 373, s2215_plain_checked⟩

def s2216_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2216_plain_checked : check 400 s2216_plain_contract = true := by decide +kernel
def s2216_plain : CertifiedContract :=
  ⟨2216, 2217, 0, (.inc 8), s2216_plain_contract, 400, s2216_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S044
