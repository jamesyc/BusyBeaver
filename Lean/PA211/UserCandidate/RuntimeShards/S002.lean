module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S002
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0095_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0095_plain_checked : check 319 s0095_plain_contract = true := by decide +kernel
def s0095_plain : CertifiedContract :=
  ⟨95, 96, 0, (.inc 2), s0095_plain_contract, 319, s0095_plain_checked⟩

def s0096_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0096_plain_checked : check 83 s0096_plain_contract = true := by decide +kernel
def s0096_plain : CertifiedContract :=
  ⟨96, 94, 0, .none, s0096_plain_contract, 83, s0096_plain_checked⟩

def s0097_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0097_plain_checked : check 86 s0097_plain_contract = true := by decide +kernel
def s0097_plain : CertifiedContract :=
  ⟨97, 88, 0, .none, s0097_plain_contract, 86, s0097_plain_checked⟩

def s0098_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, true, false] 0 .none⟩
theorem s0098_zero_checked : check 288 s0098_zero_contract = true := by decide +kernel
def s0098_zero : CertifiedContract :=
  ⟨98, 104, 0, .none, s0098_zero_contract, 288, s0098_zero_checked⟩

def s0098_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0098_positive_checked : check 288 s0098_positive_contract = true := by decide +kernel
def s0098_positive : CertifiedContract :=
  ⟨98, 99, 1, (.dec 5), s0098_positive_contract, 288, s0098_positive_checked⟩

def s0099_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0099_plain_checked : check 301 s0099_plain_contract = true := by decide +kernel
def s0099_plain : CertifiedContract :=
  ⟨99, 100, 0, (.inc 2), s0099_plain_contract, 301, s0099_plain_checked⟩

def s0100_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0100_plain_checked : check 304 s0100_plain_contract = true := by decide +kernel
def s0100_plain : CertifiedContract :=
  ⟨100, 101, 0, (.inc 2), s0100_plain_contract, 304, s0100_plain_checked⟩

def s0101_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0101_plain_checked : check 310 s0101_plain_contract = true := by decide +kernel
def s0101_plain : CertifiedContract :=
  ⟨101, 102, 0, (.inc 2), s0101_plain_contract, 310, s0101_plain_checked⟩

def s0102_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0102_plain_checked : check 316 s0102_plain_contract = true := by decide +kernel
def s0102_plain : CertifiedContract :=
  ⟨102, 103, 0, (.inc 2), s0102_plain_contract, 316, s0102_plain_checked⟩

def s0103_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s0103_plain_checked : check 71 s0103_plain_contract = true := by decide +kernel
def s0103_plain : CertifiedContract :=
  ⟨103, 98, 0, .none, s0103_plain_contract, 71, s0103_plain_checked⟩

def s0104_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0104_plain_checked : check 256 s0104_plain_contract = true := by decide +kernel
def s0104_plain : CertifiedContract :=
  ⟨104, 105, 0, (.inc 2), s0104_plain_contract, 256, s0104_plain_checked⟩

def s0105_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0105_plain_checked : check 265 s0105_plain_contract = true := by decide +kernel
def s0105_plain : CertifiedContract :=
  ⟨105, 106, 0, (.inc 2), s0105_plain_contract, 265, s0105_plain_checked⟩

def s0106_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0106_zero_checked : check 273 s0106_zero_contract = true := by decide +kernel
def s0106_zero : CertifiedContract :=
  ⟨106, 109, 0, .none, s0106_zero_contract, 273, s0106_zero_checked⟩

def s0106_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0106_positive_checked : check 279 s0106_positive_contract = true := by decide +kernel
def s0106_positive : CertifiedContract :=
  ⟨106, 107, 1, (.dec 2), s0106_positive_contract, 279, s0106_positive_checked⟩

def s0107_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0107_plain_checked : check 292 s0107_plain_contract = true := by decide +kernel
def s0107_plain : CertifiedContract :=
  ⟨107, 108, 0, (.inc 8), s0107_plain_contract, 292, s0107_plain_checked⟩

def s0108_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0108_plain_checked : check 71 s0108_plain_contract = true := by decide +kernel
def s0108_plain : CertifiedContract :=
  ⟨108, 106, 0, .none, s0108_plain_contract, 71, s0108_plain_checked⟩

def s0109_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0109_zero_checked : check 294 s0109_zero_contract = true := by decide +kernel
def s0109_zero : CertifiedContract :=
  ⟨109, 112, 0, .none, s0109_zero_contract, 294, s0109_zero_checked⟩

def s0109_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0109_positive_checked : check 300 s0109_positive_contract = true := by decide +kernel
def s0109_positive : CertifiedContract :=
  ⟨109, 110, 1, (.dec 0), s0109_positive_contract, 300, s0109_positive_checked⟩

def s0110_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0110_plain_checked : check 292 s0110_plain_contract = true := by decide +kernel
def s0110_plain : CertifiedContract :=
  ⟨110, 111, 0, (.inc 2), s0110_plain_contract, 292, s0110_plain_checked⟩

def s0111_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0111_plain_checked : check 74 s0111_plain_contract = true := by decide +kernel
def s0111_plain : CertifiedContract :=
  ⟨111, 109, 0, .none, s0111_plain_contract, 74, s0111_plain_checked⟩

def s0112_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0112_zero_checked : check 300 s0112_zero_contract = true := by decide +kernel
def s0112_zero : CertifiedContract :=
  ⟨112, 116, 0, .none, s0112_zero_contract, 300, s0112_zero_checked⟩

def s0112_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0112_positive_checked : check 306 s0112_positive_contract = true := by decide +kernel
def s0112_positive : CertifiedContract :=
  ⟨112, 113, 1, (.dec 2), s0112_positive_contract, 306, s0112_positive_checked⟩

def s0113_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0113_plain_checked : check 319 s0113_plain_contract = true := by decide +kernel
def s0113_plain : CertifiedContract :=
  ⟨113, 114, 0, (.inc 5), s0113_plain_contract, 319, s0113_plain_checked⟩

def s0114_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0114_plain_checked : check 346 s0114_plain_contract = true := by decide +kernel
def s0114_plain : CertifiedContract :=
  ⟨114, 115, 0, (.inc 8), s0114_plain_contract, 346, s0114_plain_checked⟩

def s0115_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0115_plain_checked : check 89 s0115_plain_contract = true := by decide +kernel
def s0115_plain : CertifiedContract :=
  ⟨115, 112, 0, .none, s0115_plain_contract, 89, s0115_plain_checked⟩

def s0116_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0116_zero_checked : check 321 s0116_zero_contract = true := by decide +kernel
def s0116_zero : CertifiedContract :=
  ⟨116, 122, 0, .none, s0116_zero_contract, 321, s0116_zero_checked⟩

def s0116_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0116_positive_checked : check 324 s0116_positive_contract = true := by decide +kernel
def s0116_positive : CertifiedContract :=
  ⟨116, 117, 1, (.dec 8), s0116_positive_contract, 324, s0116_positive_checked⟩

def s0117_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0117_plain_checked : check 319 s0117_plain_contract = true := by decide +kernel
def s0117_plain : CertifiedContract :=
  ⟨117, 118, 0, (.inc 5), s0117_plain_contract, 319, s0117_plain_checked⟩

def s0118_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0118_zero_checked : check 339 s0118_zero_contract = true := by decide +kernel
def s0118_zero : CertifiedContract :=
  ⟨118, 121, 0, .none, s0118_zero_contract, 339, s0118_zero_checked⟩

def s0118_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0118_positive_checked : check 342 s0118_positive_contract = true := by decide +kernel
def s0118_positive : CertifiedContract :=
  ⟨118, 119, 1, (.dec 8), s0118_positive_contract, 342, s0118_positive_checked⟩

def s0119_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0119_plain_checked : check 337 s0119_plain_contract = true := by decide +kernel
def s0119_plain : CertifiedContract :=
  ⟨119, 120, 0, (.inc 2), s0119_plain_contract, 337, s0119_plain_checked⟩

def s0120_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0120_plain_checked : check 89 s0120_plain_contract = true := by decide +kernel
def s0120_plain : CertifiedContract :=
  ⟨120, 118, 0, .none, s0120_plain_contract, 89, s0120_plain_checked⟩

def s0121_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0121_plain_checked : check 92 s0121_plain_contract = true := by decide +kernel
def s0121_plain : CertifiedContract :=
  ⟨121, 112, 0, .none, s0121_plain_contract, 92, s0121_plain_checked⟩

def s0122_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0122_zero_checked : check 309 s0122_zero_contract = true := by decide +kernel
def s0122_zero : CertifiedContract :=
  ⟨122, 125, 0, .none, s0122_zero_contract, 309, s0122_zero_checked⟩

def s0122_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0122_positive_checked : check 306 s0122_positive_contract = true := by decide +kernel
def s0122_positive : CertifiedContract :=
  ⟨122, 123, 1, (.dec 5), s0122_positive_contract, 306, s0122_positive_checked⟩

def s0123_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0123_plain_checked : check 319 s0123_plain_contract = true := by decide +kernel
def s0123_plain : CertifiedContract :=
  ⟨123, 124, 0, (.inc 0), s0123_plain_contract, 319, s0123_plain_checked⟩

def s0124_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0124_plain_checked : check 80 s0124_plain_contract = true := by decide +kernel
def s0124_plain : CertifiedContract :=
  ⟨124, 122, 0, .none, s0124_plain_contract, 80, s0124_plain_checked⟩

def s0125_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0125_zero_checked : check 273 s0125_zero_contract = true := by decide +kernel
def s0125_zero : CertifiedContract :=
  ⟨125, 129, 0, .none, s0125_zero_contract, 273, s0125_zero_checked⟩

def s0125_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s0125_positive_checked : check 279 s0125_positive_contract = true := by decide +kernel
def s0125_positive : CertifiedContract :=
  ⟨125, 126, 1, (.dec 4), s0125_positive_contract, 279, s0125_positive_checked⟩

def s0126_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0126_plain_checked : check 292 s0126_plain_contract = true := by decide +kernel
def s0126_plain : CertifiedContract :=
  ⟨126, 127, 0, (.inc 2), s0126_plain_contract, 292, s0126_plain_checked⟩

def s0127_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0127_plain_checked : check 319 s0127_plain_contract = true := by decide +kernel
def s0127_plain : CertifiedContract :=
  ⟨127, 128, 0, (.inc 8), s0127_plain_contract, 319, s0127_plain_checked⟩

def s0128_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0128_plain_checked : check 80 s0128_plain_contract = true := by decide +kernel
def s0128_plain : CertifiedContract :=
  ⟨128, 125, 0, .none, s0128_plain_contract, 80, s0128_plain_checked⟩

def s0129_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0129_zero_checked : check 279 s0129_zero_contract = true := by decide +kernel
def s0129_zero : CertifiedContract :=
  ⟨129, 132, 0, .none, s0129_zero_contract, 279, s0129_zero_checked⟩

def s0129_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0129_positive_checked : check 279 s0129_positive_contract = true := by decide +kernel
def s0129_positive : CertifiedContract :=
  ⟨129, 130, 1, (.dec 8), s0129_positive_contract, 279, s0129_positive_checked⟩

def s0130_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s0130_plain_checked : check 283 s0130_plain_contract = true := by decide +kernel
def s0130_plain : CertifiedContract :=
  ⟨130, 131, 0, (.inc 4), s0130_plain_contract, 283, s0130_plain_checked⟩

def s0131_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0131_plain_checked : check 71 s0131_plain_contract = true := by decide +kernel
def s0131_plain : CertifiedContract :=
  ⟨131, 129, 0, .none, s0131_plain_contract, 71, s0131_plain_checked⟩

def s0132_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0132_zero_checked : check 273 s0132_zero_contract = true := by decide +kernel
def s0132_zero : CertifiedContract :=
  ⟨132, 135, 0, .none, s0132_zero_contract, 273, s0132_zero_checked⟩

def s0132_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0132_positive_checked : check 279 s0132_positive_contract = true := by decide +kernel
def s0132_positive : CertifiedContract :=
  ⟨132, 133, 1, (.dec 2), s0132_positive_contract, 279, s0132_positive_checked⟩

def s0133_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0133_plain_checked : check 292 s0133_plain_contract = true := by decide +kernel
def s0133_plain : CertifiedContract :=
  ⟨133, 134, 0, (.inc 8), s0133_plain_contract, 292, s0133_plain_checked⟩

def s0134_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0134_plain_checked : check 71 s0134_plain_contract = true := by decide +kernel
def s0134_plain : CertifiedContract :=
  ⟨134, 132, 0, .none, s0134_plain_contract, 71, s0134_plain_checked⟩

def s0135_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0135_zero_checked : check 294 s0135_zero_contract = true := by decide +kernel
def s0135_zero : CertifiedContract :=
  ⟨135, 138, 0, .none, s0135_zero_contract, 294, s0135_zero_checked⟩

def s0135_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0135_positive_checked : check 300 s0135_positive_contract = true := by decide +kernel
def s0135_positive : CertifiedContract :=
  ⟨135, 136, 1, (.dec 0), s0135_positive_contract, 300, s0135_positive_checked⟩

def s0136_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0136_plain_checked : check 292 s0136_plain_contract = true := by decide +kernel
def s0136_plain : CertifiedContract :=
  ⟨136, 137, 0, (.inc 2), s0136_plain_contract, 292, s0136_plain_checked⟩

def s0137_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0137_plain_checked : check 74 s0137_plain_contract = true := by decide +kernel
def s0137_plain : CertifiedContract :=
  ⟨137, 135, 0, .none, s0137_plain_contract, 74, s0137_plain_checked⟩

def s0138_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0138_zero_checked : check 300 s0138_zero_contract = true := by decide +kernel
def s0138_zero : CertifiedContract :=
  ⟨138, 142, 0, .none, s0138_zero_contract, 300, s0138_zero_checked⟩

def s0138_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0138_positive_checked : check 306 s0138_positive_contract = true := by decide +kernel
def s0138_positive : CertifiedContract :=
  ⟨138, 139, 1, (.dec 2), s0138_positive_contract, 306, s0138_positive_checked⟩

def s0139_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0139_plain_checked : check 319 s0139_plain_contract = true := by decide +kernel
def s0139_plain : CertifiedContract :=
  ⟨139, 140, 0, (.inc 5), s0139_plain_contract, 319, s0139_plain_checked⟩

def s0140_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0140_plain_checked : check 346 s0140_plain_contract = true := by decide +kernel
def s0140_plain : CertifiedContract :=
  ⟨140, 141, 0, (.inc 8), s0140_plain_contract, 346, s0140_plain_checked⟩

def s0141_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0141_plain_checked : check 89 s0141_plain_contract = true := by decide +kernel
def s0141_plain : CertifiedContract :=
  ⟨141, 138, 0, .none, s0141_plain_contract, 89, s0141_plain_checked⟩

def s0142_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0142_zero_checked : check 321 s0142_zero_contract = true := by decide +kernel
def s0142_zero : CertifiedContract :=
  ⟨142, 148, 0, .none, s0142_zero_contract, 321, s0142_zero_checked⟩

def s0142_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0142_positive_checked : check 324 s0142_positive_contract = true := by decide +kernel
def s0142_positive : CertifiedContract :=
  ⟨142, 143, 1, (.dec 8), s0142_positive_contract, 324, s0142_positive_checked⟩

def s0143_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0143_plain_checked : check 319 s0143_plain_contract = true := by decide +kernel
def s0143_plain : CertifiedContract :=
  ⟨143, 144, 0, (.inc 5), s0143_plain_contract, 319, s0143_plain_checked⟩

def s0144_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0144_zero_checked : check 339 s0144_zero_contract = true := by decide +kernel
def s0144_zero : CertifiedContract :=
  ⟨144, 147, 0, .none, s0144_zero_contract, 339, s0144_zero_checked⟩

def s0144_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0144_positive_checked : check 342 s0144_positive_contract = true := by decide +kernel
def s0144_positive : CertifiedContract :=
  ⟨144, 145, 1, (.dec 8), s0144_positive_contract, 342, s0144_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S002
