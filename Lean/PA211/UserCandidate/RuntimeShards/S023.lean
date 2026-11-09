module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S023
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1131_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1131_plain_checked : check 104 s1131_plain_contract = true := by decide +kernel
def s1131_plain : CertifiedContract :=
  ⟨1131, 1129, 0, .none, s1131_plain_contract, 104, s1131_plain_checked⟩

def s1132_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s1132_plain_checked : check 107 s1132_plain_contract = true := by decide +kernel
def s1132_plain : CertifiedContract :=
  ⟨1132, 1123, 0, .none, s1132_plain_contract, 107, s1132_plain_checked⟩

def s1133_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, false, false] 0 .none⟩
theorem s1133_zero_checked : check 354 s1133_zero_contract = true := by decide +kernel
def s1133_zero : CertifiedContract :=
  ⟨1133, 1136, 0, .none, s1133_zero_contract, 354, s1133_zero_checked⟩

def s1133_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1133_positive_checked : check 351 s1133_positive_contract = true := by decide +kernel
def s1133_positive : CertifiedContract :=
  ⟨1133, 1134, 1, (.dec 5), s1133_positive_contract, 351, s1133_positive_checked⟩

def s1134_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1134_plain_checked : check 364 s1134_plain_contract = true := by decide +kernel
def s1134_plain : CertifiedContract :=
  ⟨1134, 1135, 0, (.inc 0), s1134_plain_contract, 364, s1134_plain_checked⟩

def s1135_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s1135_plain_checked : check 95 s1135_plain_contract = true := by decide +kernel
def s1135_plain : CertifiedContract :=
  ⟨1135, 1133, 0, .none, s1135_plain_contract, 95, s1135_plain_checked⟩

def s1136_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false] 0 .none⟩
theorem s1136_zero_checked : check 318 s1136_zero_contract = true := by decide +kernel
def s1136_zero : CertifiedContract :=
  ⟨1136, 1140, 0, .none, s1136_zero_contract, 318, s1136_zero_checked⟩

def s1136_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, false, true, false] 1 (.dec 4)⟩
theorem s1136_positive_checked : check 324 s1136_positive_contract = true := by decide +kernel
def s1136_positive : CertifiedContract :=
  ⟨1136, 1137, 1, (.dec 4), s1136_positive_contract, 324, s1136_positive_checked⟩

def s1137_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1137_plain_checked : check 337 s1137_plain_contract = true := by decide +kernel
def s1137_plain : CertifiedContract :=
  ⟨1137, 1138, 0, (.inc 2), s1137_plain_contract, 337, s1137_plain_checked⟩

def s1138_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1138_plain_checked : check 364 s1138_plain_contract = true := by decide +kernel
def s1138_plain : CertifiedContract :=
  ⟨1138, 1139, 0, (.inc 8), s1138_plain_contract, 364, s1138_plain_checked⟩

def s1139_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, false, false] 0 .none⟩
theorem s1139_plain_checked : check 95 s1139_plain_contract = true := by decide +kernel
def s1139_plain : CertifiedContract :=
  ⟨1139, 1136, 0, .none, s1139_plain_contract, 95, s1139_plain_checked⟩

def s1140_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1140_zero_checked : check 339 s1140_zero_contract = true := by decide +kernel
def s1140_zero : CertifiedContract :=
  ⟨1140, 1143, 0, .none, s1140_zero_contract, 339, s1140_zero_checked⟩

def s1140_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1140_positive_checked : check 324 s1140_positive_contract = true := by decide +kernel
def s1140_positive : CertifiedContract :=
  ⟨1140, 1141, 1, (.dec 8), s1140_positive_contract, 324, s1140_positive_checked⟩

def s1141_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, true, true] 0 (.inc 4)⟩
theorem s1141_plain_checked : check 328 s1141_plain_contract = true := by decide +kernel
def s1141_plain : CertifiedContract :=
  ⟨1141, 1142, 0, (.inc 4), s1141_plain_contract, 328, s1141_plain_checked⟩

def s1142_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false] 0 .none⟩
theorem s1142_plain_checked : check 86 s1142_plain_contract = true := by decide +kernel
def s1142_plain : CertifiedContract :=
  ⟨1142, 1140, 0, .none, s1142_plain_contract, 86, s1142_plain_checked⟩

def s1143_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, true, false] 0 .none⟩
theorem s1143_zero_checked : check 312 s1143_zero_contract = true := by decide +kernel
def s1143_zero : CertifiedContract :=
  ⟨1143, 1151, 0, .none, s1143_zero_contract, 312, s1143_zero_checked⟩

def s1143_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1143_positive_checked : check 318 s1143_positive_contract = true := by decide +kernel
def s1143_positive : CertifiedContract :=
  ⟨1143, 1144, 1, (.dec 0), s1143_positive_contract, 318, s1143_positive_checked⟩

def s1144_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1144_plain_checked : check 328 s1144_plain_contract = true := by decide +kernel
def s1144_plain : CertifiedContract :=
  ⟨1144, 1145, 0, (.inc 5), s1144_plain_contract, 328, s1144_plain_checked⟩

def s1145_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1145_zero_checked : check 354 s1145_zero_contract = true := by decide +kernel
def s1145_zero : CertifiedContract :=
  ⟨1145, 1147, 0, .none, s1145_zero_contract, 354, s1145_zero_checked⟩

def s1145_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1145_positive_checked : check 360 s1145_positive_contract = true := by decide +kernel
def s1145_positive : CertifiedContract :=
  ⟨1145, 1146, 1, (.dec 8), s1145_positive_contract, 360, s1145_positive_checked⟩

def s1146_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s1146_plain_checked : check 95 s1146_plain_contract = true := by decide +kernel
def s1146_plain : CertifiedContract :=
  ⟨1146, 1150, 0, .none, s1146_plain_contract, 95, s1146_plain_checked⟩

def s1147_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s1147_zero_checked : check 366 s1147_zero_contract = true := by decide +kernel
def s1147_zero : CertifiedContract :=
  ⟨1147, 1150, 0, .none, s1147_zero_contract, 366, s1147_zero_checked⟩

def s1147_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1147_positive_checked : check 369 s1147_positive_contract = true := by decide +kernel
def s1147_positive : CertifiedContract :=
  ⟨1147, 1148, 1, (.dec 5), s1147_positive_contract, 369, s1147_positive_checked⟩

def s1148_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1148_plain_checked : check 373 s1148_plain_contract = true := by decide +kernel
def s1148_plain : CertifiedContract :=
  ⟨1148, 1149, 0, (.inc 8), s1148_plain_contract, 373, s1148_plain_checked⟩

def s1149_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1149_plain_checked : check 98 s1149_plain_contract = true := by decide +kernel
def s1149_plain : CertifiedContract :=
  ⟨1149, 1147, 0, .none, s1149_plain_contract, 98, s1149_plain_checked⟩

def s1150_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1150_plain_checked : check 89 s1150_plain_contract = true := by decide +kernel
def s1150_plain : CertifiedContract :=
  ⟨1150, 1143, 0, .none, s1150_plain_contract, 89, s1150_plain_checked⟩

def s1151_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s1151_zero_checked : check 312 s1151_zero_contract = true := by decide +kernel
def s1151_zero : CertifiedContract :=
  ⟨1151, 1154, 0, .none, s1151_zero_contract, 312, s1151_zero_checked⟩

def s1151_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1151_positive_checked : check 315 s1151_positive_contract = true := by decide +kernel
def s1151_positive : CertifiedContract :=
  ⟨1151, 1152, 1, (.dec 5), s1151_positive_contract, 315, s1151_positive_checked⟩

def s1152_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1152_plain_checked : check 328 s1152_plain_contract = true := by decide +kernel
def s1152_plain : CertifiedContract :=
  ⟨1152, 1153, 0, (.inc 0), s1152_plain_contract, 328, s1152_plain_checked⟩

def s1153_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, false, true, false] 0 .none⟩
theorem s1153_plain_checked : check 83 s1153_plain_contract = true := by decide +kernel
def s1153_plain : CertifiedContract :=
  ⟨1153, 1151, 0, .none, s1153_plain_contract, 83, s1153_plain_checked⟩

def s1154_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, false] 0 .none⟩
theorem s1154_zero_checked : check 309 s1154_zero_contract = true := by decide +kernel
def s1154_zero : CertifiedContract :=
  ⟨1154, 1158, 0, .none, s1154_zero_contract, 309, s1154_zero_checked⟩

def s1154_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1154_positive_checked : check 315 s1154_positive_contract = true := by decide +kernel
def s1154_positive : CertifiedContract :=
  ⟨1154, 1155, 1, (.dec 2), s1154_positive_contract, 315, s1154_positive_checked⟩

def s1155_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1155_plain_checked : check 328 s1155_plain_contract = true := by decide +kernel
def s1155_plain : CertifiedContract :=
  ⟨1155, 1156, 0, (.inc 5), s1155_plain_contract, 328, s1155_plain_checked⟩

def s1156_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1156_plain_checked : check 355 s1156_plain_contract = true := by decide +kernel
def s1156_plain : CertifiedContract :=
  ⟨1156, 1157, 0, (.inc 8), s1156_plain_contract, 355, s1156_plain_checked⟩

def s1157_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s1157_plain_checked : check 92 s1157_plain_contract = true := by decide +kernel
def s1157_plain : CertifiedContract :=
  ⟨1157, 1154, 0, .none, s1157_plain_contract, 92, s1157_plain_checked⟩

def s1158_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1158_zero_checked : check 330 s1158_zero_contract = true := by decide +kernel
def s1158_zero : CertifiedContract :=
  ⟨1158, 1164, 0, .none, s1158_zero_contract, 330, s1158_zero_checked⟩

def s1158_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1158_positive_checked : check 333 s1158_positive_contract = true := by decide +kernel
def s1158_positive : CertifiedContract :=
  ⟨1158, 1159, 1, (.dec 8), s1158_positive_contract, 333, s1158_positive_checked⟩

def s1159_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1159_plain_checked : check 328 s1159_plain_contract = true := by decide +kernel
def s1159_plain : CertifiedContract :=
  ⟨1159, 1160, 0, (.inc 5), s1159_plain_contract, 328, s1159_plain_checked⟩

def s1160_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, true] 0 .none⟩
theorem s1160_zero_checked : check 348 s1160_zero_contract = true := by decide +kernel
def s1160_zero : CertifiedContract :=
  ⟨1160, 1163, 0, .none, s1160_zero_contract, 348, s1160_zero_checked⟩

def s1160_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1160_positive_checked : check 351 s1160_positive_contract = true := by decide +kernel
def s1160_positive : CertifiedContract :=
  ⟨1160, 1161, 1, (.dec 8), s1160_positive_contract, 351, s1160_positive_checked⟩

def s1161_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1161_plain_checked : check 346 s1161_plain_contract = true := by decide +kernel
def s1161_plain : CertifiedContract :=
  ⟨1161, 1162, 0, (.inc 2), s1161_plain_contract, 346, s1161_plain_checked⟩

def s1162_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1162_plain_checked : check 92 s1162_plain_contract = true := by decide +kernel
def s1162_plain : CertifiedContract :=
  ⟨1162, 1160, 0, .none, s1162_plain_contract, 92, s1162_plain_checked⟩

def s1163_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s1163_plain_checked : check 95 s1163_plain_contract = true := by decide +kernel
def s1163_plain : CertifiedContract :=
  ⟨1163, 1154, 0, .none, s1163_plain_contract, 95, s1163_plain_checked⟩

def s1164_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1164_zero_checked : check 315 s1164_zero_contract = true := by decide +kernel
def s1164_zero : CertifiedContract :=
  ⟨1164, 1170, 0, .none, s1164_zero_contract, 315, s1164_zero_checked⟩

def s1164_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1164_positive_checked : check 315 s1164_positive_contract = true := by decide +kernel
def s1164_positive : CertifiedContract :=
  ⟨1164, 1165, 1, (.dec 5), s1164_positive_contract, 315, s1164_positive_checked⟩

def s1165_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1165_plain_checked : check 328 s1165_plain_contract = true := by decide +kernel
def s1165_plain : CertifiedContract :=
  ⟨1165, 1166, 0, (.inc 2), s1165_plain_contract, 328, s1165_plain_checked⟩

def s1166_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1166_plain_checked : check 331 s1166_plain_contract = true := by decide +kernel
def s1166_plain : CertifiedContract :=
  ⟨1166, 1167, 0, (.inc 2), s1166_plain_contract, 331, s1166_plain_checked⟩

def s1167_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1167_plain_checked : check 337 s1167_plain_contract = true := by decide +kernel
def s1167_plain : CertifiedContract :=
  ⟨1167, 1168, 0, (.inc 2), s1167_plain_contract, 337, s1167_plain_checked⟩

def s1168_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1168_plain_checked : check 343 s1168_plain_contract = true := by decide +kernel
def s1168_plain : CertifiedContract :=
  ⟨1168, 1169, 0, (.inc 2), s1168_plain_contract, 343, s1168_plain_checked⟩

def s1169_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1169_plain_checked : check 80 s1169_plain_contract = true := by decide +kernel
def s1169_plain : CertifiedContract :=
  ⟨1169, 1164, 0, .none, s1169_plain_contract, 80, s1169_plain_checked⟩

def s1170_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1170_zero_checked : check 327 s1170_zero_contract = true := by decide +kernel
def s1170_zero : CertifiedContract :=
  ⟨1170, 1173, 0, .none, s1170_zero_contract, 327, s1170_zero_checked⟩

def s1170_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1170_positive_checked : check 333 s1170_positive_contract = true := by decide +kernel
def s1170_positive : CertifiedContract :=
  ⟨1170, 1171, 1, (.dec 2), s1170_positive_contract, 333, s1170_positive_checked⟩

def s1171_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1171_plain_checked : check 346 s1171_plain_contract = true := by decide +kernel
def s1171_plain : CertifiedContract :=
  ⟨1171, 1172, 0, (.inc 8), s1171_plain_contract, 346, s1171_plain_checked⟩

def s1172_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1172_plain_checked : check 89 s1172_plain_contract = true := by decide +kernel
def s1172_plain : CertifiedContract :=
  ⟨1172, 1170, 0, .none, s1172_plain_contract, 89, s1172_plain_checked⟩

def s1173_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1173_zero_checked : check 348 s1173_zero_contract = true := by decide +kernel
def s1173_zero : CertifiedContract :=
  ⟨1173, 1176, 0, .none, s1173_zero_contract, 348, s1173_zero_checked⟩

def s1173_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1173_positive_checked : check 354 s1173_positive_contract = true := by decide +kernel
def s1173_positive : CertifiedContract :=
  ⟨1173, 1174, 1, (.dec 0), s1173_positive_contract, 354, s1173_positive_checked⟩

def s1174_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1174_plain_checked : check 346 s1174_plain_contract = true := by decide +kernel
def s1174_plain : CertifiedContract :=
  ⟨1174, 1175, 0, (.inc 2), s1174_plain_contract, 346, s1174_plain_checked⟩

def s1175_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1175_plain_checked : check 92 s1175_plain_contract = true := by decide +kernel
def s1175_plain : CertifiedContract :=
  ⟨1175, 1173, 0, .none, s1175_plain_contract, 92, s1175_plain_checked⟩

def s1176_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1176_zero_checked : check 354 s1176_zero_contract = true := by decide +kernel
def s1176_zero : CertifiedContract :=
  ⟨1176, 1180, 0, .none, s1176_zero_contract, 354, s1176_zero_checked⟩

def s1176_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1176_positive_checked : check 360 s1176_positive_contract = true := by decide +kernel
def s1176_positive : CertifiedContract :=
  ⟨1176, 1177, 1, (.dec 2), s1176_positive_contract, 360, s1176_positive_checked⟩

def s1177_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1177_plain_checked : check 373 s1177_plain_contract = true := by decide +kernel
def s1177_plain : CertifiedContract :=
  ⟨1177, 1178, 0, (.inc 5), s1177_plain_contract, 373, s1177_plain_checked⟩

def s1178_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1178_plain_checked : check 400 s1178_plain_contract = true := by decide +kernel
def s1178_plain : CertifiedContract :=
  ⟨1178, 1179, 0, (.inc 8), s1178_plain_contract, 400, s1178_plain_checked⟩

def s1179_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1179_plain_checked : check 107 s1179_plain_contract = true := by decide +kernel
def s1179_plain : CertifiedContract :=
  ⟨1179, 1176, 0, .none, s1179_plain_contract, 107, s1179_plain_checked⟩

def s1180_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1180_zero_checked : check 375 s1180_zero_contract = true := by decide +kernel
def s1180_zero : CertifiedContract :=
  ⟨1180, 1186, 0, .none, s1180_zero_contract, 375, s1180_zero_checked⟩

end PA211.UserCandidate.RuntimeShards.S023
