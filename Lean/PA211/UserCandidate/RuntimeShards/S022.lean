import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S022
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1082_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1082_zero_checked : check 420 s1082_zero_contract = true := by decide +kernel
def s1082_zero : CertifiedContract :=
  ⟨1082, 1085, 0, .none, s1082_zero_contract, 420, s1082_zero_checked⟩

def s1082_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1082_positive_checked : check 423 s1082_positive_contract = true := by decide +kernel
def s1082_positive : CertifiedContract :=
  ⟨1082, 1083, 1, (.dec 8), s1082_positive_contract, 423, s1082_positive_checked⟩

def s1083_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1083_plain_checked : check 418 s1083_plain_contract = true := by decide +kernel
def s1083_plain : CertifiedContract :=
  ⟨1083, 1084, 0, (.inc 2), s1083_plain_contract, 418, s1083_plain_checked⟩

def s1084_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1084_plain_checked : check 116 s1084_plain_contract = true := by decide +kernel
def s1084_plain : CertifiedContract :=
  ⟨1084, 1082, 0, .none, s1084_plain_contract, 116, s1084_plain_checked⟩

def s1085_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s1085_plain_checked : check 119 s1085_plain_contract = true := by decide +kernel
def s1085_plain : CertifiedContract :=
  ⟨1085, 1076, 0, .none, s1085_plain_contract, 119, s1085_plain_checked⟩

def s1086_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, true] 0 .none⟩
theorem s1086_zero_checked : check 390 s1086_zero_contract = true := by decide +kernel
def s1086_zero : CertifiedContract :=
  ⟨1086, 1089, 0, .none, s1086_zero_contract, 390, s1086_zero_checked⟩

def s1086_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1086_positive_checked : check 387 s1086_positive_contract = true := by decide +kernel
def s1086_positive : CertifiedContract :=
  ⟨1086, 1087, 1, (.dec 5), s1086_positive_contract, 387, s1086_positive_checked⟩

def s1087_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1087_plain_checked : check 400 s1087_plain_contract = true := by decide +kernel
def s1087_plain : CertifiedContract :=
  ⟨1087, 1088, 0, (.inc 0), s1087_plain_contract, 400, s1087_plain_checked⟩

def s1088_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s1088_plain_checked : check 107 s1088_plain_contract = true := by decide +kernel
def s1088_plain : CertifiedContract :=
  ⟨1088, 1086, 0, .none, s1088_plain_contract, 107, s1088_plain_checked⟩

def s1089_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, false] 0 (.inc 2)⟩
theorem s1089_plain_checked : check 340 s1089_plain_contract = true := by decide +kernel
def s1089_plain : CertifiedContract :=
  ⟨1089, 1090, 0, (.inc 2), s1089_plain_contract, 340, s1089_plain_checked⟩

def s1090_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, false] 0 .none⟩
theorem s1090_zero_checked : check 357 s1090_zero_contract = true := by decide +kernel
def s1090_zero : CertifiedContract :=
  ⟨1090, 1098, 0, .none, s1090_zero_contract, 357, s1090_zero_checked⟩

def s1090_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false] 1 (.dec 0)⟩
theorem s1090_positive_checked : check 363 s1090_positive_contract = true := by decide +kernel
def s1090_positive : CertifiedContract :=
  ⟨1090, 1091, 1, (.dec 0), s1090_positive_contract, 363, s1090_positive_checked⟩

def s1091_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1091_plain_checked : check 373 s1091_plain_contract = true := by decide +kernel
def s1091_plain : CertifiedContract :=
  ⟨1091, 1092, 0, (.inc 5), s1091_plain_contract, 373, s1091_plain_checked⟩

def s1092_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1092_zero_checked : check 399 s1092_zero_contract = true := by decide +kernel
def s1092_zero : CertifiedContract :=
  ⟨1092, 1094, 0, .none, s1092_zero_contract, 399, s1092_zero_checked⟩

def s1092_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1092_positive_checked : check 405 s1092_positive_contract = true := by decide +kernel
def s1092_positive : CertifiedContract :=
  ⟨1092, 1093, 1, (.dec 8), s1092_positive_contract, 405, s1092_positive_checked⟩

def s1093_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s1093_plain_checked : check 110 s1093_plain_contract = true := by decide +kernel
def s1093_plain : CertifiedContract :=
  ⟨1093, 1097, 0, .none, s1093_plain_contract, 110, s1093_plain_checked⟩

def s1094_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s1094_zero_checked : check 411 s1094_zero_contract = true := by decide +kernel
def s1094_zero : CertifiedContract :=
  ⟨1094, 1097, 0, .none, s1094_zero_contract, 411, s1094_zero_checked⟩

def s1094_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1094_positive_checked : check 414 s1094_positive_contract = true := by decide +kernel
def s1094_positive : CertifiedContract :=
  ⟨1094, 1095, 1, (.dec 5), s1094_positive_contract, 414, s1094_positive_checked⟩

def s1095_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1095_plain_checked : check 418 s1095_plain_contract = true := by decide +kernel
def s1095_plain : CertifiedContract :=
  ⟨1095, 1096, 0, (.inc 8), s1095_plain_contract, 418, s1095_plain_checked⟩

def s1096_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1096_plain_checked : check 113 s1096_plain_contract = true := by decide +kernel
def s1096_plain : CertifiedContract :=
  ⟨1096, 1094, 0, .none, s1096_plain_contract, 113, s1096_plain_checked⟩

def s1097_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s1097_plain_checked : check 104 s1097_plain_contract = true := by decide +kernel
def s1097_plain : CertifiedContract :=
  ⟨1097, 1090, 0, .none, s1097_plain_contract, 104, s1097_plain_checked⟩

def s1098_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s1098_zero_checked : check 357 s1098_zero_contract = true := by decide +kernel
def s1098_zero : CertifiedContract :=
  ⟨1098, 1101, 0, .none, s1098_zero_contract, 357, s1098_zero_checked⟩

def s1098_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1098_positive_checked : check 360 s1098_positive_contract = true := by decide +kernel
def s1098_positive : CertifiedContract :=
  ⟨1098, 1099, 1, (.dec 5), s1098_positive_contract, 360, s1098_positive_checked⟩

def s1099_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s1099_plain_checked : check 373 s1099_plain_contract = true := by decide +kernel
def s1099_plain : CertifiedContract :=
  ⟨1099, 1100, 0, (.inc 0), s1099_plain_contract, 373, s1099_plain_checked⟩

def s1100_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, false] 0 .none⟩
theorem s1100_plain_checked : check 98 s1100_plain_contract = true := by decide +kernel
def s1100_plain : CertifiedContract :=
  ⟨1100, 1098, 0, .none, s1100_plain_contract, 98, s1100_plain_checked⟩

def s1101_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s1101_zero_checked : check 354 s1101_zero_contract = true := by decide +kernel
def s1101_zero : CertifiedContract :=
  ⟨1101, 1105, 0, .none, s1101_zero_contract, 354, s1101_zero_checked⟩

def s1101_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1101_positive_checked : check 360 s1101_positive_contract = true := by decide +kernel
def s1101_positive : CertifiedContract :=
  ⟨1101, 1102, 1, (.dec 2), s1101_positive_contract, 360, s1101_positive_checked⟩

def s1102_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1102_plain_checked : check 373 s1102_plain_contract = true := by decide +kernel
def s1102_plain : CertifiedContract :=
  ⟨1102, 1103, 0, (.inc 5), s1102_plain_contract, 373, s1102_plain_checked⟩

def s1103_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1103_plain_checked : check 400 s1103_plain_contract = true := by decide +kernel
def s1103_plain : CertifiedContract :=
  ⟨1103, 1104, 0, (.inc 8), s1103_plain_contract, 400, s1103_plain_checked⟩

def s1104_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s1104_plain_checked : check 107 s1104_plain_contract = true := by decide +kernel
def s1104_plain : CertifiedContract :=
  ⟨1104, 1101, 0, .none, s1104_plain_contract, 107, s1104_plain_checked⟩

def s1105_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, false] 0 .none⟩
theorem s1105_zero_checked : check 375 s1105_zero_contract = true := by decide +kernel
def s1105_zero : CertifiedContract :=
  ⟨1105, 1111, 0, .none, s1105_zero_contract, 375, s1105_zero_checked⟩

def s1105_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1105_positive_checked : check 378 s1105_positive_contract = true := by decide +kernel
def s1105_positive : CertifiedContract :=
  ⟨1105, 1106, 1, (.dec 8), s1105_positive_contract, 378, s1105_positive_checked⟩

def s1106_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1106_plain_checked : check 373 s1106_plain_contract = true := by decide +kernel
def s1106_plain : CertifiedContract :=
  ⟨1106, 1107, 0, (.inc 5), s1106_plain_contract, 373, s1106_plain_checked⟩

def s1107_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, true] 0 .none⟩
theorem s1107_zero_checked : check 393 s1107_zero_contract = true := by decide +kernel
def s1107_zero : CertifiedContract :=
  ⟨1107, 1110, 0, .none, s1107_zero_contract, 393, s1107_zero_checked⟩

def s1107_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1107_positive_checked : check 396 s1107_positive_contract = true := by decide +kernel
def s1107_positive : CertifiedContract :=
  ⟨1107, 1108, 1, (.dec 8), s1107_positive_contract, 396, s1107_positive_checked⟩

def s1108_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1108_plain_checked : check 391 s1108_plain_contract = true := by decide +kernel
def s1108_plain : CertifiedContract :=
  ⟨1108, 1109, 0, (.inc 2), s1108_plain_contract, 391, s1108_plain_checked⟩

def s1109_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1109_plain_checked : check 107 s1109_plain_contract = true := by decide +kernel
def s1109_plain : CertifiedContract :=
  ⟨1109, 1107, 0, .none, s1109_plain_contract, 107, s1109_plain_checked⟩

def s1110_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s1110_plain_checked : check 110 s1110_plain_contract = true := by decide +kernel
def s1110_plain : CertifiedContract :=
  ⟨1110, 1101, 0, .none, s1110_plain_contract, 110, s1110_plain_checked⟩

def s1111_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s1111_zero_checked : check 369 s1111_zero_contract = true := by decide +kernel
def s1111_zero : CertifiedContract :=
  ⟨1111, 1117, 0, .none, s1111_zero_contract, 369, s1111_zero_checked⟩

def s1111_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1111_positive_checked : check 360 s1111_positive_contract = true := by decide +kernel
def s1111_positive : CertifiedContract :=
  ⟨1111, 1112, 1, (.dec 5), s1111_positive_contract, 360, s1111_positive_checked⟩

def s1112_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1112_plain_checked : check 373 s1112_plain_contract = true := by decide +kernel
def s1112_plain : CertifiedContract :=
  ⟨1112, 1113, 0, (.inc 2), s1112_plain_contract, 373, s1112_plain_checked⟩

def s1113_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1113_plain_checked : check 376 s1113_plain_contract = true := by decide +kernel
def s1113_plain : CertifiedContract :=
  ⟨1113, 1114, 0, (.inc 2), s1113_plain_contract, 376, s1113_plain_checked⟩

def s1114_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1114_plain_checked : check 382 s1114_plain_contract = true := by decide +kernel
def s1114_plain : CertifiedContract :=
  ⟨1114, 1115, 0, (.inc 2), s1114_plain_contract, 382, s1114_plain_checked⟩

def s1115_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s1115_plain_checked : check 388 s1115_plain_contract = true := by decide +kernel
def s1115_plain : CertifiedContract :=
  ⟨1115, 1116, 0, (.inc 2), s1115_plain_contract, 388, s1115_plain_checked⟩

def s1116_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, false] 0 .none⟩
theorem s1116_plain_checked : check 95 s1116_plain_contract = true := by decide +kernel
def s1116_plain : CertifiedContract :=
  ⟨1116, 1111, 0, .none, s1116_plain_contract, 95, s1116_plain_checked⟩

def s1117_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s1117_zero_checked : check 318 s1117_zero_contract = true := by decide +kernel
def s1117_zero : CertifiedContract :=
  ⟨1117, 1120, 0, .none, s1117_zero_contract, 318, s1117_zero_checked⟩

def s1117_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1117_positive_checked : check 324 s1117_positive_contract = true := by decide +kernel
def s1117_positive : CertifiedContract :=
  ⟨1117, 1118, 1, (.dec 2), s1117_positive_contract, 324, s1117_positive_checked⟩

def s1118_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1118_plain_checked : check 337 s1118_plain_contract = true := by decide +kernel
def s1118_plain : CertifiedContract :=
  ⟨1118, 1119, 0, (.inc 8), s1118_plain_contract, 337, s1118_plain_checked⟩

def s1119_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s1119_plain_checked : check 86 s1119_plain_contract = true := by decide +kernel
def s1119_plain : CertifiedContract :=
  ⟨1119, 1117, 0, .none, s1119_plain_contract, 86, s1119_plain_checked⟩

def s1120_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s1120_zero_checked : check 339 s1120_zero_contract = true := by decide +kernel
def s1120_zero : CertifiedContract :=
  ⟨1120, 1123, 0, .none, s1120_zero_contract, 339, s1120_zero_checked⟩

def s1120_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1120_positive_checked : check 345 s1120_positive_contract = true := by decide +kernel
def s1120_positive : CertifiedContract :=
  ⟨1120, 1121, 1, (.dec 0), s1120_positive_contract, 345, s1120_positive_checked⟩

def s1121_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1121_plain_checked : check 337 s1121_plain_contract = true := by decide +kernel
def s1121_plain : CertifiedContract :=
  ⟨1121, 1122, 0, (.inc 2), s1121_plain_contract, 337, s1121_plain_checked⟩

def s1122_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s1122_plain_checked : check 89 s1122_plain_contract = true := by decide +kernel
def s1122_plain : CertifiedContract :=
  ⟨1122, 1120, 0, .none, s1122_plain_contract, 89, s1122_plain_checked⟩

def s1123_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1123_zero_checked : check 345 s1123_zero_contract = true := by decide +kernel
def s1123_zero : CertifiedContract :=
  ⟨1123, 1127, 0, .none, s1123_zero_contract, 345, s1123_zero_checked⟩

def s1123_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1123_positive_checked : check 351 s1123_positive_contract = true := by decide +kernel
def s1123_positive : CertifiedContract :=
  ⟨1123, 1124, 1, (.dec 2), s1123_positive_contract, 351, s1123_positive_checked⟩

def s1124_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1124_plain_checked : check 364 s1124_plain_contract = true := by decide +kernel
def s1124_plain : CertifiedContract :=
  ⟨1124, 1125, 0, (.inc 5), s1124_plain_contract, 364, s1124_plain_checked⟩

def s1125_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1125_plain_checked : check 391 s1125_plain_contract = true := by decide +kernel
def s1125_plain : CertifiedContract :=
  ⟨1125, 1126, 0, (.inc 8), s1125_plain_contract, 391, s1125_plain_checked⟩

def s1126_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s1126_plain_checked : check 104 s1126_plain_contract = true := by decide +kernel
def s1126_plain : CertifiedContract :=
  ⟨1126, 1123, 0, .none, s1126_plain_contract, 104, s1126_plain_checked⟩

def s1127_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s1127_zero_checked : check 366 s1127_zero_contract = true := by decide +kernel
def s1127_zero : CertifiedContract :=
  ⟨1127, 1133, 0, .none, s1127_zero_contract, 366, s1127_zero_checked⟩

def s1127_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1127_positive_checked : check 369 s1127_positive_contract = true := by decide +kernel
def s1127_positive : CertifiedContract :=
  ⟨1127, 1128, 1, (.dec 8), s1127_positive_contract, 369, s1127_positive_checked⟩

def s1128_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1128_plain_checked : check 364 s1128_plain_contract = true := by decide +kernel
def s1128_plain : CertifiedContract :=
  ⟨1128, 1129, 0, (.inc 5), s1128_plain_contract, 364, s1128_plain_checked⟩

def s1129_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1129_zero_checked : check 384 s1129_zero_contract = true := by decide +kernel
def s1129_zero : CertifiedContract :=
  ⟨1129, 1132, 0, .none, s1129_zero_contract, 384, s1129_zero_checked⟩

def s1129_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1129_positive_checked : check 387 s1129_positive_contract = true := by decide +kernel
def s1129_positive : CertifiedContract :=
  ⟨1129, 1130, 1, (.dec 8), s1129_positive_contract, 387, s1129_positive_checked⟩

def s1130_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1130_plain_checked : check 382 s1130_plain_contract = true := by decide +kernel
def s1130_plain : CertifiedContract :=
  ⟨1130, 1131, 0, (.inc 2), s1130_plain_contract, 382, s1130_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S022
