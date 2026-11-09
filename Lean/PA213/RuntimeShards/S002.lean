module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S002
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0095_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0095_plain_checked : check 318 s0095_plain_contract = true := by decide +kernel
def s0095_plain : CertifiedContract :=
  ⟨95, 96, 0, (.inc 2), s0095_plain_contract, 318, s0095_plain_checked⟩

def s0096_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0096_plain_checked : check 82 s0096_plain_contract = true := by decide +kernel
def s0096_plain : CertifiedContract :=
  ⟨96, 94, 0, .none, s0096_plain_contract, 82, s0096_plain_checked⟩

def s0097_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0097_plain_checked : check 85 s0097_plain_contract = true := by decide +kernel
def s0097_plain : CertifiedContract :=
  ⟨97, 88, 0, .none, s0097_plain_contract, 85, s0097_plain_checked⟩

def s0098_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, true, false] 0 .none⟩
theorem s0098_zero_checked : check 287 s0098_zero_contract = true := by decide +kernel
def s0098_zero : CertifiedContract :=
  ⟨98, 104, 0, .none, s0098_zero_contract, 287, s0098_zero_checked⟩

def s0098_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0098_positive_checked : check 287 s0098_positive_contract = true := by decide +kernel
def s0098_positive : CertifiedContract :=
  ⟨98, 99, 1, (.dec 5), s0098_positive_contract, 287, s0098_positive_checked⟩

def s0099_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0099_plain_checked : check 300 s0099_plain_contract = true := by decide +kernel
def s0099_plain : CertifiedContract :=
  ⟨99, 100, 0, (.inc 2), s0099_plain_contract, 300, s0099_plain_checked⟩

def s0100_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0100_plain_checked : check 303 s0100_plain_contract = true := by decide +kernel
def s0100_plain : CertifiedContract :=
  ⟨100, 101, 0, (.inc 2), s0100_plain_contract, 303, s0100_plain_checked⟩

def s0101_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0101_plain_checked : check 300 s0101_plain_contract = true := by decide +kernel
def s0101_plain : CertifiedContract :=
  ⟨101, 102, 0, (.inc 2), s0101_plain_contract, 300, s0101_plain_checked⟩

def s0102_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0102_plain_checked : check 306 s0102_plain_contract = true := by decide +kernel
def s0102_plain : CertifiedContract :=
  ⟨102, 103, 0, (.inc 2), s0102_plain_contract, 306, s0102_plain_checked⟩

def s0103_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s0103_plain_checked : check 70 s0103_plain_contract = true := by decide +kernel
def s0103_plain : CertifiedContract :=
  ⟨103, 98, 0, .none, s0103_plain_contract, 70, s0103_plain_checked⟩

def s0104_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0104_plain_checked : check 255 s0104_plain_contract = true := by decide +kernel
def s0104_plain : CertifiedContract :=
  ⟨104, 105, 0, (.inc 2), s0104_plain_contract, 255, s0104_plain_checked⟩

def s0105_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0105_plain_checked : check 264 s0105_plain_contract = true := by decide +kernel
def s0105_plain : CertifiedContract :=
  ⟨105, 106, 0, (.inc 2), s0105_plain_contract, 264, s0105_plain_checked⟩

def s0106_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0106_zero_checked : check 272 s0106_zero_contract = true := by decide +kernel
def s0106_zero : CertifiedContract :=
  ⟨106, 109, 0, .none, s0106_zero_contract, 272, s0106_zero_checked⟩

def s0106_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0106_positive_checked : check 278 s0106_positive_contract = true := by decide +kernel
def s0106_positive : CertifiedContract :=
  ⟨106, 107, 1, (.dec 2), s0106_positive_contract, 278, s0106_positive_checked⟩

def s0107_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0107_plain_checked : check 291 s0107_plain_contract = true := by decide +kernel
def s0107_plain : CertifiedContract :=
  ⟨107, 108, 0, (.inc 8), s0107_plain_contract, 291, s0107_plain_checked⟩

def s0108_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0108_plain_checked : check 70 s0108_plain_contract = true := by decide +kernel
def s0108_plain : CertifiedContract :=
  ⟨108, 106, 0, .none, s0108_plain_contract, 70, s0108_plain_checked⟩

def s0109_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0109_zero_checked : check 293 s0109_zero_contract = true := by decide +kernel
def s0109_zero : CertifiedContract :=
  ⟨109, 112, 0, .none, s0109_zero_contract, 293, s0109_zero_checked⟩

def s0109_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0109_positive_checked : check 299 s0109_positive_contract = true := by decide +kernel
def s0109_positive : CertifiedContract :=
  ⟨109, 110, 1, (.dec 0), s0109_positive_contract, 299, s0109_positive_checked⟩

def s0110_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0110_plain_checked : check 291 s0110_plain_contract = true := by decide +kernel
def s0110_plain : CertifiedContract :=
  ⟨110, 111, 0, (.inc 2), s0110_plain_contract, 291, s0110_plain_checked⟩

def s0111_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0111_plain_checked : check 73 s0111_plain_contract = true := by decide +kernel
def s0111_plain : CertifiedContract :=
  ⟨111, 109, 0, .none, s0111_plain_contract, 73, s0111_plain_checked⟩

def s0112_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0112_zero_checked : check 299 s0112_zero_contract = true := by decide +kernel
def s0112_zero : CertifiedContract :=
  ⟨112, 116, 0, .none, s0112_zero_contract, 299, s0112_zero_checked⟩

def s0112_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0112_positive_checked : check 305 s0112_positive_contract = true := by decide +kernel
def s0112_positive : CertifiedContract :=
  ⟨112, 113, 1, (.dec 2), s0112_positive_contract, 305, s0112_positive_checked⟩

def s0113_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0113_plain_checked : check 318 s0113_plain_contract = true := by decide +kernel
def s0113_plain : CertifiedContract :=
  ⟨113, 114, 0, (.inc 5), s0113_plain_contract, 318, s0113_plain_checked⟩

def s0114_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0114_plain_checked : check 345 s0114_plain_contract = true := by decide +kernel
def s0114_plain : CertifiedContract :=
  ⟨114, 115, 0, (.inc 8), s0114_plain_contract, 345, s0114_plain_checked⟩

def s0115_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0115_plain_checked : check 88 s0115_plain_contract = true := by decide +kernel
def s0115_plain : CertifiedContract :=
  ⟨115, 112, 0, .none, s0115_plain_contract, 88, s0115_plain_checked⟩

def s0116_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0116_zero_checked : check 320 s0116_zero_contract = true := by decide +kernel
def s0116_zero : CertifiedContract :=
  ⟨116, 122, 0, .none, s0116_zero_contract, 320, s0116_zero_checked⟩

def s0116_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0116_positive_checked : check 323 s0116_positive_contract = true := by decide +kernel
def s0116_positive : CertifiedContract :=
  ⟨116, 117, 1, (.dec 8), s0116_positive_contract, 323, s0116_positive_checked⟩

def s0117_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0117_plain_checked : check 318 s0117_plain_contract = true := by decide +kernel
def s0117_plain : CertifiedContract :=
  ⟨117, 118, 0, (.inc 5), s0117_plain_contract, 318, s0117_plain_checked⟩

def s0118_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0118_zero_checked : check 338 s0118_zero_contract = true := by decide +kernel
def s0118_zero : CertifiedContract :=
  ⟨118, 121, 0, .none, s0118_zero_contract, 338, s0118_zero_checked⟩

def s0118_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0118_positive_checked : check 341 s0118_positive_contract = true := by decide +kernel
def s0118_positive : CertifiedContract :=
  ⟨118, 119, 1, (.dec 8), s0118_positive_contract, 341, s0118_positive_checked⟩

def s0119_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0119_plain_checked : check 336 s0119_plain_contract = true := by decide +kernel
def s0119_plain : CertifiedContract :=
  ⟨119, 120, 0, (.inc 2), s0119_plain_contract, 336, s0119_plain_checked⟩

def s0120_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0120_plain_checked : check 88 s0120_plain_contract = true := by decide +kernel
def s0120_plain : CertifiedContract :=
  ⟨120, 118, 0, .none, s0120_plain_contract, 88, s0120_plain_checked⟩

def s0121_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0121_plain_checked : check 91 s0121_plain_contract = true := by decide +kernel
def s0121_plain : CertifiedContract :=
  ⟨121, 112, 0, .none, s0121_plain_contract, 91, s0121_plain_checked⟩

def s0122_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0122_zero_checked : check 308 s0122_zero_contract = true := by decide +kernel
def s0122_zero : CertifiedContract :=
  ⟨122, 125, 0, .none, s0122_zero_contract, 308, s0122_zero_checked⟩

def s0122_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0122_positive_checked : check 305 s0122_positive_contract = true := by decide +kernel
def s0122_positive : CertifiedContract :=
  ⟨122, 123, 1, (.dec 5), s0122_positive_contract, 305, s0122_positive_checked⟩

def s0123_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0123_plain_checked : check 318 s0123_plain_contract = true := by decide +kernel
def s0123_plain : CertifiedContract :=
  ⟨123, 124, 0, (.inc 0), s0123_plain_contract, 318, s0123_plain_checked⟩

def s0124_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0124_plain_checked : check 79 s0124_plain_contract = true := by decide +kernel
def s0124_plain : CertifiedContract :=
  ⟨124, 122, 0, .none, s0124_plain_contract, 79, s0124_plain_checked⟩

def s0125_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0125_zero_checked : check 272 s0125_zero_contract = true := by decide +kernel
def s0125_zero : CertifiedContract :=
  ⟨125, 129, 0, .none, s0125_zero_contract, 272, s0125_zero_checked⟩

def s0125_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s0125_positive_checked : check 278 s0125_positive_contract = true := by decide +kernel
def s0125_positive : CertifiedContract :=
  ⟨125, 126, 1, (.dec 4), s0125_positive_contract, 278, s0125_positive_checked⟩

def s0126_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0126_plain_checked : check 291 s0126_plain_contract = true := by decide +kernel
def s0126_plain : CertifiedContract :=
  ⟨126, 127, 0, (.inc 2), s0126_plain_contract, 291, s0126_plain_checked⟩

def s0127_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0127_plain_checked : check 318 s0127_plain_contract = true := by decide +kernel
def s0127_plain : CertifiedContract :=
  ⟨127, 128, 0, (.inc 8), s0127_plain_contract, 318, s0127_plain_checked⟩

def s0128_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0128_plain_checked : check 79 s0128_plain_contract = true := by decide +kernel
def s0128_plain : CertifiedContract :=
  ⟨128, 125, 0, .none, s0128_plain_contract, 79, s0128_plain_checked⟩

def s0129_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0129_zero_checked : check 278 s0129_zero_contract = true := by decide +kernel
def s0129_zero : CertifiedContract :=
  ⟨129, 132, 0, .none, s0129_zero_contract, 278, s0129_zero_checked⟩

def s0129_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0129_positive_checked : check 278 s0129_positive_contract = true := by decide +kernel
def s0129_positive : CertifiedContract :=
  ⟨129, 130, 1, (.dec 8), s0129_positive_contract, 278, s0129_positive_checked⟩

def s0130_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s0130_plain_checked : check 282 s0130_plain_contract = true := by decide +kernel
def s0130_plain : CertifiedContract :=
  ⟨130, 131, 0, (.inc 4), s0130_plain_contract, 282, s0130_plain_checked⟩

def s0131_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0131_plain_checked : check 70 s0131_plain_contract = true := by decide +kernel
def s0131_plain : CertifiedContract :=
  ⟨131, 129, 0, .none, s0131_plain_contract, 70, s0131_plain_checked⟩

def s0132_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0132_zero_checked : check 272 s0132_zero_contract = true := by decide +kernel
def s0132_zero : CertifiedContract :=
  ⟨132, 135, 0, .none, s0132_zero_contract, 272, s0132_zero_checked⟩

def s0132_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0132_positive_checked : check 278 s0132_positive_contract = true := by decide +kernel
def s0132_positive : CertifiedContract :=
  ⟨132, 133, 1, (.dec 2), s0132_positive_contract, 278, s0132_positive_checked⟩

def s0133_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0133_plain_checked : check 291 s0133_plain_contract = true := by decide +kernel
def s0133_plain : CertifiedContract :=
  ⟨133, 134, 0, (.inc 8), s0133_plain_contract, 291, s0133_plain_checked⟩

def s0134_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0134_plain_checked : check 70 s0134_plain_contract = true := by decide +kernel
def s0134_plain : CertifiedContract :=
  ⟨134, 132, 0, .none, s0134_plain_contract, 70, s0134_plain_checked⟩

def s0135_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0135_zero_checked : check 293 s0135_zero_contract = true := by decide +kernel
def s0135_zero : CertifiedContract :=
  ⟨135, 138, 0, .none, s0135_zero_contract, 293, s0135_zero_checked⟩

def s0135_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0135_positive_checked : check 299 s0135_positive_contract = true := by decide +kernel
def s0135_positive : CertifiedContract :=
  ⟨135, 136, 1, (.dec 0), s0135_positive_contract, 299, s0135_positive_checked⟩

def s0136_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0136_plain_checked : check 291 s0136_plain_contract = true := by decide +kernel
def s0136_plain : CertifiedContract :=
  ⟨136, 137, 0, (.inc 2), s0136_plain_contract, 291, s0136_plain_checked⟩

def s0137_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0137_plain_checked : check 73 s0137_plain_contract = true := by decide +kernel
def s0137_plain : CertifiedContract :=
  ⟨137, 135, 0, .none, s0137_plain_contract, 73, s0137_plain_checked⟩

def s0138_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0138_zero_checked : check 299 s0138_zero_contract = true := by decide +kernel
def s0138_zero : CertifiedContract :=
  ⟨138, 142, 0, .none, s0138_zero_contract, 299, s0138_zero_checked⟩

def s0138_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0138_positive_checked : check 305 s0138_positive_contract = true := by decide +kernel
def s0138_positive : CertifiedContract :=
  ⟨138, 139, 1, (.dec 2), s0138_positive_contract, 305, s0138_positive_checked⟩

def s0139_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0139_plain_checked : check 318 s0139_plain_contract = true := by decide +kernel
def s0139_plain : CertifiedContract :=
  ⟨139, 140, 0, (.inc 5), s0139_plain_contract, 318, s0139_plain_checked⟩

def s0140_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0140_plain_checked : check 345 s0140_plain_contract = true := by decide +kernel
def s0140_plain : CertifiedContract :=
  ⟨140, 141, 0, (.inc 8), s0140_plain_contract, 345, s0140_plain_checked⟩

def s0141_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0141_plain_checked : check 88 s0141_plain_contract = true := by decide +kernel
def s0141_plain : CertifiedContract :=
  ⟨141, 138, 0, .none, s0141_plain_contract, 88, s0141_plain_checked⟩

def s0142_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0142_zero_checked : check 320 s0142_zero_contract = true := by decide +kernel
def s0142_zero : CertifiedContract :=
  ⟨142, 148, 0, .none, s0142_zero_contract, 320, s0142_zero_checked⟩

def s0142_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0142_positive_checked : check 323 s0142_positive_contract = true := by decide +kernel
def s0142_positive : CertifiedContract :=
  ⟨142, 143, 1, (.dec 8), s0142_positive_contract, 323, s0142_positive_checked⟩

def s0143_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0143_plain_checked : check 318 s0143_plain_contract = true := by decide +kernel
def s0143_plain : CertifiedContract :=
  ⟨143, 144, 0, (.inc 5), s0143_plain_contract, 318, s0143_plain_checked⟩

def s0144_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0144_zero_checked : check 338 s0144_zero_contract = true := by decide +kernel
def s0144_zero : CertifiedContract :=
  ⟨144, 147, 0, .none, s0144_zero_contract, 338, s0144_zero_checked⟩

def s0144_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0144_positive_checked : check 341 s0144_positive_contract = true := by decide +kernel
def s0144_positive : CertifiedContract :=
  ⟨144, 145, 1, (.dec 8), s0144_positive_contract, 341, s0144_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0095_plain,
  s0096_plain,
  s0097_plain,
  s0098_zero,
  s0098_positive,
  s0099_plain,
  s0100_plain,
  s0101_plain,
  s0102_plain,
  s0103_plain,
  s0104_plain,
  s0105_plain,
  s0106_zero,
  s0106_positive,
  s0107_plain,
  s0108_plain,
  s0109_zero,
  s0109_positive,
  s0110_plain,
  s0111_plain,
  s0112_zero,
  s0112_positive,
  s0113_plain,
  s0114_plain,
  s0115_plain,
  s0116_zero,
  s0116_positive,
  s0117_plain,
  s0118_zero,
  s0118_positive,
  s0119_plain,
  s0120_plain,
  s0121_plain,
  s0122_zero,
  s0122_positive,
  s0123_plain,
  s0124_plain,
  s0125_zero,
  s0125_positive,
  s0126_plain,
  s0127_plain,
  s0128_plain,
  s0129_zero,
  s0129_positive,
  s0130_plain,
  s0131_plain,
  s0132_zero,
  s0132_positive,
  s0133_plain,
  s0134_plain,
  s0135_zero,
  s0135_positive,
  s0136_plain,
  s0137_plain,
  s0138_zero,
  s0138_positive,
  s0139_plain,
  s0140_plain,
  s0141_plain,
  s0142_zero,
  s0142_positive,
  s0143_plain,
  s0144_zero,
  s0144_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S002
