import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S021
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1031_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1031_positive_checked : check 405 s1031_positive_contract = true := by decide +kernel
def s1031_positive : CertifiedContract :=
  ⟨1031, 1032, 1, (.dec 8), s1031_positive_contract, 405, s1031_positive_checked⟩

def s1032_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1032_plain_checked : check 400 s1032_plain_contract = true := by decide +kernel
def s1032_plain : CertifiedContract :=
  ⟨1032, 1033, 0, (.inc 2), s1032_plain_contract, 400, s1032_plain_checked⟩

def s1033_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1033_plain_checked : check 110 s1033_plain_contract = true := by decide +kernel
def s1033_plain : CertifiedContract :=
  ⟨1033, 1031, 0, .none, s1033_plain_contract, 110, s1033_plain_checked⟩

def s1034_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1034_plain_checked : check 113 s1034_plain_contract = true := by decide +kernel
def s1034_plain : CertifiedContract :=
  ⟨1034, 1025, 0, .none, s1034_plain_contract, 113, s1034_plain_checked⟩

def s1035_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1035_zero_checked : check 369 s1035_zero_contract = true := by decide +kernel
def s1035_zero : CertifiedContract :=
  ⟨1035, 1041, 0, .none, s1035_zero_contract, 369, s1035_zero_checked⟩

def s1035_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1035_positive_checked : check 369 s1035_positive_contract = true := by decide +kernel
def s1035_positive : CertifiedContract :=
  ⟨1035, 1036, 1, (.dec 5), s1035_positive_contract, 369, s1035_positive_checked⟩

def s1036_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1036_plain_checked : check 382 s1036_plain_contract = true := by decide +kernel
def s1036_plain : CertifiedContract :=
  ⟨1036, 1037, 0, (.inc 2), s1036_plain_contract, 382, s1036_plain_checked⟩

def s1037_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1037_plain_checked : check 385 s1037_plain_contract = true := by decide +kernel
def s1037_plain : CertifiedContract :=
  ⟨1037, 1038, 0, (.inc 2), s1037_plain_contract, 385, s1037_plain_checked⟩

def s1038_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1038_plain_checked : check 391 s1038_plain_contract = true := by decide +kernel
def s1038_plain : CertifiedContract :=
  ⟨1038, 1039, 0, (.inc 2), s1038_plain_contract, 391, s1038_plain_checked⟩

def s1039_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1039_plain_checked : check 397 s1039_plain_contract = true := by decide +kernel
def s1039_plain : CertifiedContract :=
  ⟨1039, 1040, 0, (.inc 2), s1039_plain_contract, 397, s1039_plain_checked⟩

def s1040_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, false] 0 .none⟩
theorem s1040_plain_checked : check 98 s1040_plain_contract = true := by decide +kernel
def s1040_plain : CertifiedContract :=
  ⟨1040, 1035, 0, .none, s1040_plain_contract, 98, s1040_plain_checked⟩

def s1041_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1041_zero_checked : check 375 s1041_zero_contract = true := by decide +kernel
def s1041_zero : CertifiedContract :=
  ⟨1041, 1049, 0, .none, s1041_zero_contract, 375, s1041_zero_checked⟩

def s1041_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1041_positive_checked : check 381 s1041_positive_contract = true := by decide +kernel
def s1041_positive : CertifiedContract :=
  ⟨1041, 1042, 1, (.dec 0), s1041_positive_contract, 381, s1041_positive_checked⟩

def s1042_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1042_plain_checked : check 391 s1042_plain_contract = true := by decide +kernel
def s1042_plain : CertifiedContract :=
  ⟨1042, 1043, 0, (.inc 5), s1042_plain_contract, 391, s1042_plain_checked⟩

def s1043_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1043_zero_checked : check 417 s1043_zero_contract = true := by decide +kernel
def s1043_zero : CertifiedContract :=
  ⟨1043, 1045, 0, .none, s1043_zero_contract, 417, s1043_zero_checked⟩

def s1043_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1043_positive_checked : check 423 s1043_positive_contract = true := by decide +kernel
def s1043_positive : CertifiedContract :=
  ⟨1043, 1044, 1, (.dec 8), s1043_positive_contract, 423, s1043_positive_checked⟩

def s1044_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1044_plain_checked : check 116 s1044_plain_contract = true := by decide +kernel
def s1044_plain : CertifiedContract :=
  ⟨1044, 1048, 0, .none, s1044_plain_contract, 116, s1044_plain_checked⟩

def s1045_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1045_zero_checked : check 429 s1045_zero_contract = true := by decide +kernel
def s1045_zero : CertifiedContract :=
  ⟨1045, 1048, 0, .none, s1045_zero_contract, 429, s1045_zero_checked⟩

def s1045_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1045_positive_checked : check 432 s1045_positive_contract = true := by decide +kernel
def s1045_positive : CertifiedContract :=
  ⟨1045, 1046, 1, (.dec 5), s1045_positive_contract, 432, s1045_positive_checked⟩

def s1046_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1046_plain_checked : check 436 s1046_plain_contract = true := by decide +kernel
def s1046_plain : CertifiedContract :=
  ⟨1046, 1047, 0, (.inc 8), s1046_plain_contract, 436, s1046_plain_checked⟩

def s1047_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1047_plain_checked : check 119 s1047_plain_contract = true := by decide +kernel
def s1047_plain : CertifiedContract :=
  ⟨1047, 1045, 0, .none, s1047_plain_contract, 119, s1047_plain_checked⟩

def s1048_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1048_plain_checked : check 110 s1048_plain_contract = true := by decide +kernel
def s1048_plain : CertifiedContract :=
  ⟨1048, 1041, 0, .none, s1048_plain_contract, 110, s1048_plain_checked⟩

def s1049_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1049_zero_checked : check 375 s1049_zero_contract = true := by decide +kernel
def s1049_zero : CertifiedContract :=
  ⟨1049, 1052, 0, .none, s1049_zero_contract, 375, s1049_zero_checked⟩

def s1049_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1049_positive_checked : check 378 s1049_positive_contract = true := by decide +kernel
def s1049_positive : CertifiedContract :=
  ⟨1049, 1050, 1, (.dec 5), s1049_positive_contract, 378, s1049_positive_checked⟩

def s1050_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1050_plain_checked : check 391 s1050_plain_contract = true := by decide +kernel
def s1050_plain : CertifiedContract :=
  ⟨1050, 1051, 0, (.inc 0), s1050_plain_contract, 391, s1050_plain_checked⟩

def s1051_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1051_plain_checked : check 104 s1051_plain_contract = true := by decide +kernel
def s1051_plain : CertifiedContract :=
  ⟨1051, 1049, 0, .none, s1051_plain_contract, 104, s1051_plain_checked⟩

def s1052_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s1052_zero_checked : check 372 s1052_zero_contract = true := by decide +kernel
def s1052_zero : CertifiedContract :=
  ⟨1052, 1056, 0, .none, s1052_zero_contract, 372, s1052_zero_checked⟩

def s1052_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1052_positive_checked : check 378 s1052_positive_contract = true := by decide +kernel
def s1052_positive : CertifiedContract :=
  ⟨1052, 1053, 1, (.dec 2), s1052_positive_contract, 378, s1052_positive_checked⟩

def s1053_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1053_plain_checked : check 391 s1053_plain_contract = true := by decide +kernel
def s1053_plain : CertifiedContract :=
  ⟨1053, 1054, 0, (.inc 5), s1053_plain_contract, 391, s1053_plain_checked⟩

def s1054_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1054_plain_checked : check 418 s1054_plain_contract = true := by decide +kernel
def s1054_plain : CertifiedContract :=
  ⟨1054, 1055, 0, (.inc 8), s1054_plain_contract, 418, s1054_plain_checked⟩

def s1055_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1055_plain_checked : check 113 s1055_plain_contract = true := by decide +kernel
def s1055_plain : CertifiedContract :=
  ⟨1055, 1052, 0, .none, s1055_plain_contract, 113, s1055_plain_checked⟩

def s1056_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1056_zero_checked : check 393 s1056_zero_contract = true := by decide +kernel
def s1056_zero : CertifiedContract :=
  ⟨1056, 1062, 0, .none, s1056_zero_contract, 393, s1056_zero_checked⟩

def s1056_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1056_positive_checked : check 396 s1056_positive_contract = true := by decide +kernel
def s1056_positive : CertifiedContract :=
  ⟨1056, 1057, 1, (.dec 8), s1056_positive_contract, 396, s1056_positive_checked⟩

def s1057_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1057_plain_checked : check 391 s1057_plain_contract = true := by decide +kernel
def s1057_plain : CertifiedContract :=
  ⟨1057, 1058, 0, (.inc 5), s1057_plain_contract, 391, s1057_plain_checked⟩

def s1058_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s1058_zero_checked : check 411 s1058_zero_contract = true := by decide +kernel
def s1058_zero : CertifiedContract :=
  ⟨1058, 1061, 0, .none, s1058_zero_contract, 411, s1058_zero_checked⟩

def s1058_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1058_positive_checked : check 414 s1058_positive_contract = true := by decide +kernel
def s1058_positive : CertifiedContract :=
  ⟨1058, 1059, 1, (.dec 8), s1058_positive_contract, 414, s1058_positive_checked⟩

def s1059_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1059_plain_checked : check 409 s1059_plain_contract = true := by decide +kernel
def s1059_plain : CertifiedContract :=
  ⟨1059, 1060, 0, (.inc 2), s1059_plain_contract, 409, s1059_plain_checked⟩

def s1060_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1060_plain_checked : check 113 s1060_plain_contract = true := by decide +kernel
def s1060_plain : CertifiedContract :=
  ⟨1060, 1058, 0, .none, s1060_plain_contract, 113, s1060_plain_checked⟩

def s1061_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1061_plain_checked : check 116 s1061_plain_contract = true := by decide +kernel
def s1061_plain : CertifiedContract :=
  ⟨1061, 1052, 0, .none, s1061_plain_contract, 116, s1061_plain_checked⟩

def s1062_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s1062_zero_checked : check 378 s1062_zero_contract = true := by decide +kernel
def s1062_zero : CertifiedContract :=
  ⟨1062, 1068, 0, .none, s1062_zero_contract, 378, s1062_zero_checked⟩

def s1062_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1062_positive_checked : check 378 s1062_positive_contract = true := by decide +kernel
def s1062_positive : CertifiedContract :=
  ⟨1062, 1063, 1, (.dec 5), s1062_positive_contract, 378, s1062_positive_checked⟩

def s1063_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1063_plain_checked : check 391 s1063_plain_contract = true := by decide +kernel
def s1063_plain : CertifiedContract :=
  ⟨1063, 1064, 0, (.inc 2), s1063_plain_contract, 391, s1063_plain_checked⟩

def s1064_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1064_plain_checked : check 394 s1064_plain_contract = true := by decide +kernel
def s1064_plain : CertifiedContract :=
  ⟨1064, 1065, 0, (.inc 2), s1064_plain_contract, 394, s1064_plain_checked⟩

def s1065_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1065_plain_checked : check 400 s1065_plain_contract = true := by decide +kernel
def s1065_plain : CertifiedContract :=
  ⟨1065, 1066, 0, (.inc 2), s1065_plain_contract, 400, s1065_plain_checked⟩

def s1066_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1066_plain_checked : check 406 s1066_plain_contract = true := by decide +kernel
def s1066_plain : CertifiedContract :=
  ⟨1066, 1067, 0, (.inc 2), s1066_plain_contract, 406, s1066_plain_checked⟩

def s1067_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1067_plain_checked : check 101 s1067_plain_contract = true := by decide +kernel
def s1067_plain : CertifiedContract :=
  ⟨1067, 1062, 0, .none, s1067_plain_contract, 101, s1067_plain_checked⟩

def s1068_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1068_plain_checked : check 346 s1068_plain_contract = true := by decide +kernel
def s1068_plain : CertifiedContract :=
  ⟨1068, 1069, 0, (.inc 2), s1068_plain_contract, 346, s1068_plain_checked⟩

def s1069_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, false] 0 (.inc 2)⟩
theorem s1069_plain_checked : check 355 s1069_plain_contract = true := by decide +kernel
def s1069_plain : CertifiedContract :=
  ⟨1069, 1070, 0, (.inc 2), s1069_plain_contract, 355, s1069_plain_checked⟩

def s1070_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false] 0 .none⟩
theorem s1070_zero_checked : check 354 s1070_zero_contract = true := by decide +kernel
def s1070_zero : CertifiedContract :=
  ⟨1070, 1073, 0, .none, s1070_zero_contract, 354, s1070_zero_checked⟩

def s1070_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1070_positive_checked : check 360 s1070_positive_contract = true := by decide +kernel
def s1070_positive : CertifiedContract :=
  ⟨1070, 1071, 1, (.dec 2), s1070_positive_contract, 360, s1070_positive_checked⟩

def s1071_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1071_plain_checked : check 373 s1071_plain_contract = true := by decide +kernel
def s1071_plain : CertifiedContract :=
  ⟨1071, 1072, 0, (.inc 8), s1071_plain_contract, 373, s1071_plain_checked⟩

def s1072_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, false] 0 .none⟩
theorem s1072_plain_checked : check 98 s1072_plain_contract = true := by decide +kernel
def s1072_plain : CertifiedContract :=
  ⟨1072, 1070, 0, .none, s1072_plain_contract, 98, s1072_plain_checked⟩

def s1073_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s1073_zero_checked : check 375 s1073_zero_contract = true := by decide +kernel
def s1073_zero : CertifiedContract :=
  ⟨1073, 1076, 0, .none, s1073_zero_contract, 375, s1073_zero_checked⟩

def s1073_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1073_positive_checked : check 381 s1073_positive_contract = true := by decide +kernel
def s1073_positive : CertifiedContract :=
  ⟨1073, 1074, 1, (.dec 0), s1073_positive_contract, 381, s1073_positive_checked⟩

def s1074_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1074_plain_checked : check 373 s1074_plain_contract = true := by decide +kernel
def s1074_plain : CertifiedContract :=
  ⟨1074, 1075, 0, (.inc 2), s1074_plain_contract, 373, s1074_plain_checked⟩

def s1075_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false] 0 .none⟩
theorem s1075_plain_checked : check 101 s1075_plain_contract = true := by decide +kernel
def s1075_plain : CertifiedContract :=
  ⟨1075, 1073, 0, .none, s1075_plain_contract, 101, s1075_plain_checked⟩

def s1076_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1076_zero_checked : check 381 s1076_zero_contract = true := by decide +kernel
def s1076_zero : CertifiedContract :=
  ⟨1076, 1080, 0, .none, s1076_zero_contract, 381, s1076_zero_checked⟩

def s1076_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1076_positive_checked : check 387 s1076_positive_contract = true := by decide +kernel
def s1076_positive : CertifiedContract :=
  ⟨1076, 1077, 1, (.dec 2), s1076_positive_contract, 387, s1076_positive_checked⟩

def s1077_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1077_plain_checked : check 400 s1077_plain_contract = true := by decide +kernel
def s1077_plain : CertifiedContract :=
  ⟨1077, 1078, 0, (.inc 5), s1077_plain_contract, 400, s1077_plain_checked⟩

def s1078_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1078_plain_checked : check 427 s1078_plain_contract = true := by decide +kernel
def s1078_plain : CertifiedContract :=
  ⟨1078, 1079, 0, (.inc 8), s1078_plain_contract, 427, s1078_plain_checked⟩

def s1079_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s1079_plain_checked : check 116 s1079_plain_contract = true := by decide +kernel
def s1079_plain : CertifiedContract :=
  ⟨1079, 1076, 0, .none, s1079_plain_contract, 116, s1079_plain_checked⟩

def s1080_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s1080_zero_checked : check 402 s1080_zero_contract = true := by decide +kernel
def s1080_zero : CertifiedContract :=
  ⟨1080, 1086, 0, .none, s1080_zero_contract, 402, s1080_zero_checked⟩

def s1080_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1080_positive_checked : check 405 s1080_positive_contract = true := by decide +kernel
def s1080_positive : CertifiedContract :=
  ⟨1080, 1081, 1, (.dec 8), s1080_positive_contract, 405, s1080_positive_checked⟩

def s1081_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1081_plain_checked : check 400 s1081_plain_contract = true := by decide +kernel
def s1081_plain : CertifiedContract :=
  ⟨1081, 1082, 0, (.inc 5), s1081_plain_contract, 400, s1081_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S021
