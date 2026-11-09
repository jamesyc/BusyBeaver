module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S024
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1180_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1180_positive_checked : check 378 s1180_positive_contract = true := by decide +kernel
def s1180_positive : CertifiedContract :=
  ⟨1180, 1181, 1, (.dec 8), s1180_positive_contract, 378, s1180_positive_checked⟩

def s1181_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1181_plain_checked : check 373 s1181_plain_contract = true := by decide +kernel
def s1181_plain : CertifiedContract :=
  ⟨1181, 1182, 0, (.inc 5), s1181_plain_contract, 373, s1181_plain_checked⟩

def s1182_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1182_zero_checked : check 393 s1182_zero_contract = true := by decide +kernel
def s1182_zero : CertifiedContract :=
  ⟨1182, 1185, 0, .none, s1182_zero_contract, 393, s1182_zero_checked⟩

def s1182_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1182_positive_checked : check 396 s1182_positive_contract = true := by decide +kernel
def s1182_positive : CertifiedContract :=
  ⟨1182, 1183, 1, (.dec 8), s1182_positive_contract, 396, s1182_positive_checked⟩

def s1183_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1183_plain_checked : check 391 s1183_plain_contract = true := by decide +kernel
def s1183_plain : CertifiedContract :=
  ⟨1183, 1184, 0, (.inc 2), s1183_plain_contract, 391, s1183_plain_checked⟩

def s1184_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1184_plain_checked : check 107 s1184_plain_contract = true := by decide +kernel
def s1184_plain : CertifiedContract :=
  ⟨1184, 1182, 0, .none, s1184_plain_contract, 107, s1184_plain_checked⟩

def s1185_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1185_plain_checked : check 110 s1185_plain_contract = true := by decide +kernel
def s1185_plain : CertifiedContract :=
  ⟨1185, 1176, 0, .none, s1185_plain_contract, 110, s1185_plain_checked⟩

def s1186_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1186_zero_checked : check 363 s1186_zero_contract = true := by decide +kernel
def s1186_zero : CertifiedContract :=
  ⟨1186, 1189, 0, .none, s1186_zero_contract, 363, s1186_zero_checked⟩

def s1186_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1186_positive_checked : check 360 s1186_positive_contract = true := by decide +kernel
def s1186_positive : CertifiedContract :=
  ⟨1186, 1187, 1, (.dec 5), s1186_positive_contract, 360, s1186_positive_checked⟩

def s1187_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1187_plain_checked : check 373 s1187_plain_contract = true := by decide +kernel
def s1187_plain : CertifiedContract :=
  ⟨1187, 1188, 0, (.inc 0), s1187_plain_contract, 373, s1187_plain_checked⟩

def s1188_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1188_plain_checked : check 98 s1188_plain_contract = true := by decide +kernel
def s1188_plain : CertifiedContract :=
  ⟨1188, 1186, 0, .none, s1188_plain_contract, 98, s1188_plain_checked⟩

def s1189_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1189_zero_checked : check 327 s1189_zero_contract = true := by decide +kernel
def s1189_zero : CertifiedContract :=
  ⟨1189, 1193, 0, .none, s1189_zero_contract, 327, s1189_zero_checked⟩

def s1189_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s1189_positive_checked : check 333 s1189_positive_contract = true := by decide +kernel
def s1189_positive : CertifiedContract :=
  ⟨1189, 1190, 1, (.dec 4), s1189_positive_contract, 333, s1189_positive_checked⟩

def s1190_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1190_plain_checked : check 346 s1190_plain_contract = true := by decide +kernel
def s1190_plain : CertifiedContract :=
  ⟨1190, 1191, 0, (.inc 2), s1190_plain_contract, 346, s1190_plain_checked⟩

def s1191_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1191_plain_checked : check 373 s1191_plain_contract = true := by decide +kernel
def s1191_plain : CertifiedContract :=
  ⟨1191, 1192, 0, (.inc 8), s1191_plain_contract, 373, s1191_plain_checked⟩

def s1192_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1192_plain_checked : check 98 s1192_plain_contract = true := by decide +kernel
def s1192_plain : CertifiedContract :=
  ⟨1192, 1189, 0, .none, s1192_plain_contract, 98, s1192_plain_checked⟩

def s1193_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1193_zero_checked : check 333 s1193_zero_contract = true := by decide +kernel
def s1193_zero : CertifiedContract :=
  ⟨1193, 1196, 0, .none, s1193_zero_contract, 333, s1193_zero_checked⟩

def s1193_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1193_positive_checked : check 333 s1193_positive_contract = true := by decide +kernel
def s1193_positive : CertifiedContract :=
  ⟨1193, 1194, 1, (.dec 8), s1193_positive_contract, 333, s1193_positive_checked⟩

def s1194_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s1194_plain_checked : check 337 s1194_plain_contract = true := by decide +kernel
def s1194_plain : CertifiedContract :=
  ⟨1194, 1195, 0, (.inc 4), s1194_plain_contract, 337, s1194_plain_checked⟩

def s1195_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1195_plain_checked : check 89 s1195_plain_contract = true := by decide +kernel
def s1195_plain : CertifiedContract :=
  ⟨1195, 1193, 0, .none, s1195_plain_contract, 89, s1195_plain_checked⟩

def s1196_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1196_zero_checked : check 327 s1196_zero_contract = true := by decide +kernel
def s1196_zero : CertifiedContract :=
  ⟨1196, 1199, 0, .none, s1196_zero_contract, 327, s1196_zero_checked⟩

def s1196_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1196_positive_checked : check 333 s1196_positive_contract = true := by decide +kernel
def s1196_positive : CertifiedContract :=
  ⟨1196, 1197, 1, (.dec 2), s1196_positive_contract, 333, s1196_positive_checked⟩

def s1197_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1197_plain_checked : check 346 s1197_plain_contract = true := by decide +kernel
def s1197_plain : CertifiedContract :=
  ⟨1197, 1198, 0, (.inc 8), s1197_plain_contract, 346, s1197_plain_checked⟩

def s1198_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1198_plain_checked : check 89 s1198_plain_contract = true := by decide +kernel
def s1198_plain : CertifiedContract :=
  ⟨1198, 1196, 0, .none, s1198_plain_contract, 89, s1198_plain_checked⟩

def s1199_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1199_zero_checked : check 348 s1199_zero_contract = true := by decide +kernel
def s1199_zero : CertifiedContract :=
  ⟨1199, 1202, 0, .none, s1199_zero_contract, 348, s1199_zero_checked⟩

def s1199_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1199_positive_checked : check 354 s1199_positive_contract = true := by decide +kernel
def s1199_positive : CertifiedContract :=
  ⟨1199, 1200, 1, (.dec 0), s1199_positive_contract, 354, s1199_positive_checked⟩

def s1200_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1200_plain_checked : check 346 s1200_plain_contract = true := by decide +kernel
def s1200_plain : CertifiedContract :=
  ⟨1200, 1201, 0, (.inc 2), s1200_plain_contract, 346, s1200_plain_checked⟩

def s1201_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1201_plain_checked : check 92 s1201_plain_contract = true := by decide +kernel
def s1201_plain : CertifiedContract :=
  ⟨1201, 1199, 0, .none, s1201_plain_contract, 92, s1201_plain_checked⟩

def s1202_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1202_zero_checked : check 354 s1202_zero_contract = true := by decide +kernel
def s1202_zero : CertifiedContract :=
  ⟨1202, 1206, 0, .none, s1202_zero_contract, 354, s1202_zero_checked⟩

def s1202_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1202_positive_checked : check 360 s1202_positive_contract = true := by decide +kernel
def s1202_positive : CertifiedContract :=
  ⟨1202, 1203, 1, (.dec 2), s1202_positive_contract, 360, s1202_positive_checked⟩

def s1203_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1203_plain_checked : check 373 s1203_plain_contract = true := by decide +kernel
def s1203_plain : CertifiedContract :=
  ⟨1203, 1204, 0, (.inc 5), s1203_plain_contract, 373, s1203_plain_checked⟩

def s1204_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1204_plain_checked : check 400 s1204_plain_contract = true := by decide +kernel
def s1204_plain : CertifiedContract :=
  ⟨1204, 1205, 0, (.inc 8), s1204_plain_contract, 400, s1204_plain_checked⟩

def s1205_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1205_plain_checked : check 107 s1205_plain_contract = true := by decide +kernel
def s1205_plain : CertifiedContract :=
  ⟨1205, 1202, 0, .none, s1205_plain_contract, 107, s1205_plain_checked⟩

def s1206_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1206_zero_checked : check 375 s1206_zero_contract = true := by decide +kernel
def s1206_zero : CertifiedContract :=
  ⟨1206, 1212, 0, .none, s1206_zero_contract, 375, s1206_zero_checked⟩

def s1206_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1206_positive_checked : check 378 s1206_positive_contract = true := by decide +kernel
def s1206_positive : CertifiedContract :=
  ⟨1206, 1207, 1, (.dec 8), s1206_positive_contract, 378, s1206_positive_checked⟩

def s1207_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1207_plain_checked : check 373 s1207_plain_contract = true := by decide +kernel
def s1207_plain : CertifiedContract :=
  ⟨1207, 1208, 0, (.inc 5), s1207_plain_contract, 373, s1207_plain_checked⟩

def s1208_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1208_zero_checked : check 393 s1208_zero_contract = true := by decide +kernel
def s1208_zero : CertifiedContract :=
  ⟨1208, 1211, 0, .none, s1208_zero_contract, 393, s1208_zero_checked⟩

def s1208_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1208_positive_checked : check 396 s1208_positive_contract = true := by decide +kernel
def s1208_positive : CertifiedContract :=
  ⟨1208, 1209, 1, (.dec 8), s1208_positive_contract, 396, s1208_positive_checked⟩

def s1209_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1209_plain_checked : check 391 s1209_plain_contract = true := by decide +kernel
def s1209_plain : CertifiedContract :=
  ⟨1209, 1210, 0, (.inc 2), s1209_plain_contract, 391, s1209_plain_checked⟩

def s1210_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1210_plain_checked : check 107 s1210_plain_contract = true := by decide +kernel
def s1210_plain : CertifiedContract :=
  ⟨1210, 1208, 0, .none, s1210_plain_contract, 107, s1210_plain_checked⟩

def s1211_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1211_plain_checked : check 110 s1211_plain_contract = true := by decide +kernel
def s1211_plain : CertifiedContract :=
  ⟨1211, 1202, 0, .none, s1211_plain_contract, 110, s1211_plain_checked⟩

def s1212_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1212_zero_checked : check 363 s1212_zero_contract = true := by decide +kernel
def s1212_zero : CertifiedContract :=
  ⟨1212, 1215, 0, .none, s1212_zero_contract, 363, s1212_zero_checked⟩

def s1212_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1212_positive_checked : check 360 s1212_positive_contract = true := by decide +kernel
def s1212_positive : CertifiedContract :=
  ⟨1212, 1213, 1, (.dec 5), s1212_positive_contract, 360, s1212_positive_checked⟩

def s1213_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1213_plain_checked : check 373 s1213_plain_contract = true := by decide +kernel
def s1213_plain : CertifiedContract :=
  ⟨1213, 1214, 0, (.inc 0), s1213_plain_contract, 373, s1213_plain_checked⟩

def s1214_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1214_plain_checked : check 98 s1214_plain_contract = true := by decide +kernel
def s1214_plain : CertifiedContract :=
  ⟨1214, 1212, 0, .none, s1214_plain_contract, 98, s1214_plain_checked⟩

def s1215_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1215_zero_checked : check 327 s1215_zero_contract = true := by decide +kernel
def s1215_zero : CertifiedContract :=
  ⟨1215, 1219, 0, .none, s1215_zero_contract, 327, s1215_zero_checked⟩

def s1215_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, false] 1 (.dec 3)⟩
theorem s1215_positive_checked : check 333 s1215_positive_contract = true := by decide +kernel
def s1215_positive : CertifiedContract :=
  ⟨1215, 1216, 1, (.dec 3), s1215_positive_contract, 333, s1215_positive_checked⟩

def s1216_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1216_plain_checked : check 346 s1216_plain_contract = true := by decide +kernel
def s1216_plain : CertifiedContract :=
  ⟨1216, 1217, 0, (.inc 2), s1216_plain_contract, 346, s1216_plain_checked⟩

def s1217_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1217_plain_checked : check 373 s1217_plain_contract = true := by decide +kernel
def s1217_plain : CertifiedContract :=
  ⟨1217, 1218, 0, (.inc 8), s1217_plain_contract, 373, s1217_plain_checked⟩

def s1218_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1218_plain_checked : check 98 s1218_plain_contract = true := by decide +kernel
def s1218_plain : CertifiedContract :=
  ⟨1218, 1215, 0, .none, s1218_plain_contract, 98, s1218_plain_checked⟩

def s1219_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1219_zero_checked : check 336 s1219_zero_contract = true := by decide +kernel
def s1219_zero : CertifiedContract :=
  ⟨1219, 1222, 0, .none, s1219_zero_contract, 336, s1219_zero_checked⟩

def s1219_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1219_positive_checked : check 333 s1219_positive_contract = true := by decide +kernel
def s1219_positive : CertifiedContract :=
  ⟨1219, 1220, 1, (.dec 8), s1219_positive_contract, 333, s1219_positive_checked⟩

def s1220_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, true] 0 (.inc 3)⟩
theorem s1220_plain_checked : check 349 s1220_plain_contract = true := by decide +kernel
def s1220_plain : CertifiedContract :=
  ⟨1220, 1221, 0, (.inc 3), s1220_plain_contract, 349, s1220_plain_checked⟩

def s1221_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1221_plain_checked : check 89 s1221_plain_contract = true := by decide +kernel
def s1221_plain : CertifiedContract :=
  ⟨1221, 1219, 0, .none, s1221_plain_contract, 89, s1221_plain_checked⟩

def s1222_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1222_zero_checked : check 339 s1222_zero_contract = true := by decide +kernel
def s1222_zero : CertifiedContract :=
  ⟨1222, 1230, 0, .none, s1222_zero_contract, 339, s1222_zero_checked⟩

def s1222_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1222_positive_checked : check 345 s1222_positive_contract = true := by decide +kernel
def s1222_positive : CertifiedContract :=
  ⟨1222, 1223, 1, (.dec 0), s1222_positive_contract, 345, s1222_positive_checked⟩

def s1223_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1223_plain_checked : check 355 s1223_plain_contract = true := by decide +kernel
def s1223_plain : CertifiedContract :=
  ⟨1223, 1224, 0, (.inc 5), s1223_plain_contract, 355, s1223_plain_checked⟩

def s1224_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1224_zero_checked : check 381 s1224_zero_contract = true := by decide +kernel
def s1224_zero : CertifiedContract :=
  ⟨1224, 1226, 0, .none, s1224_zero_contract, 381, s1224_zero_checked⟩

def s1224_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1224_positive_checked : check 387 s1224_positive_contract = true := by decide +kernel
def s1224_positive : CertifiedContract :=
  ⟨1224, 1225, 1, (.dec 8), s1224_positive_contract, 387, s1224_positive_checked⟩

def s1225_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1225_plain_checked : check 104 s1225_plain_contract = true := by decide +kernel
def s1225_plain : CertifiedContract :=
  ⟨1225, 1229, 0, .none, s1225_plain_contract, 104, s1225_plain_checked⟩

def s1226_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1226_zero_checked : check 393 s1226_zero_contract = true := by decide +kernel
def s1226_zero : CertifiedContract :=
  ⟨1226, 1229, 0, .none, s1226_zero_contract, 393, s1226_zero_checked⟩

def s1226_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1226_positive_checked : check 396 s1226_positive_contract = true := by decide +kernel
def s1226_positive : CertifiedContract :=
  ⟨1226, 1227, 1, (.dec 5), s1226_positive_contract, 396, s1226_positive_checked⟩

def s1227_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1227_plain_checked : check 400 s1227_plain_contract = true := by decide +kernel
def s1227_plain : CertifiedContract :=
  ⟨1227, 1228, 0, (.inc 8), s1227_plain_contract, 400, s1227_plain_checked⟩

def s1228_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1228_plain_checked : check 107 s1228_plain_contract = true := by decide +kernel
def s1228_plain : CertifiedContract :=
  ⟨1228, 1226, 0, .none, s1228_plain_contract, 107, s1228_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S024
