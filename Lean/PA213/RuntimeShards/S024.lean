module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S024
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s1180_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1180_positive_checked : check 377 s1180_positive_contract = true := by decide +kernel
def s1180_positive : CertifiedContract :=
  ⟨1180, 1181, 1, (.dec 8), s1180_positive_contract, 377, s1180_positive_checked⟩

def s1181_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1181_plain_checked : check 372 s1181_plain_contract = true := by decide +kernel
def s1181_plain : CertifiedContract :=
  ⟨1181, 1182, 0, (.inc 5), s1181_plain_contract, 372, s1181_plain_checked⟩

def s1182_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1182_zero_checked : check 392 s1182_zero_contract = true := by decide +kernel
def s1182_zero : CertifiedContract :=
  ⟨1182, 1185, 0, .none, s1182_zero_contract, 392, s1182_zero_checked⟩

def s1182_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1182_positive_checked : check 395 s1182_positive_contract = true := by decide +kernel
def s1182_positive : CertifiedContract :=
  ⟨1182, 1183, 1, (.dec 8), s1182_positive_contract, 395, s1182_positive_checked⟩

def s1183_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1183_plain_checked : check 390 s1183_plain_contract = true := by decide +kernel
def s1183_plain : CertifiedContract :=
  ⟨1183, 1184, 0, (.inc 2), s1183_plain_contract, 390, s1183_plain_checked⟩

def s1184_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1184_plain_checked : check 106 s1184_plain_contract = true := by decide +kernel
def s1184_plain : CertifiedContract :=
  ⟨1184, 1182, 0, .none, s1184_plain_contract, 106, s1184_plain_checked⟩

def s1185_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1185_plain_checked : check 109 s1185_plain_contract = true := by decide +kernel
def s1185_plain : CertifiedContract :=
  ⟨1185, 1176, 0, .none, s1185_plain_contract, 109, s1185_plain_checked⟩

def s1186_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1186_zero_checked : check 362 s1186_zero_contract = true := by decide +kernel
def s1186_zero : CertifiedContract :=
  ⟨1186, 1189, 0, .none, s1186_zero_contract, 362, s1186_zero_checked⟩

def s1186_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1186_positive_checked : check 359 s1186_positive_contract = true := by decide +kernel
def s1186_positive : CertifiedContract :=
  ⟨1186, 1187, 1, (.dec 5), s1186_positive_contract, 359, s1186_positive_checked⟩

def s1187_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1187_plain_checked : check 372 s1187_plain_contract = true := by decide +kernel
def s1187_plain : CertifiedContract :=
  ⟨1187, 1188, 0, (.inc 0), s1187_plain_contract, 372, s1187_plain_checked⟩

def s1188_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1188_plain_checked : check 97 s1188_plain_contract = true := by decide +kernel
def s1188_plain : CertifiedContract :=
  ⟨1188, 1186, 0, .none, s1188_plain_contract, 97, s1188_plain_checked⟩

def s1189_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1189_zero_checked : check 326 s1189_zero_contract = true := by decide +kernel
def s1189_zero : CertifiedContract :=
  ⟨1189, 1193, 0, .none, s1189_zero_contract, 326, s1189_zero_checked⟩

def s1189_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s1189_positive_checked : check 332 s1189_positive_contract = true := by decide +kernel
def s1189_positive : CertifiedContract :=
  ⟨1189, 1190, 1, (.dec 4), s1189_positive_contract, 332, s1189_positive_checked⟩

def s1190_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1190_plain_checked : check 345 s1190_plain_contract = true := by decide +kernel
def s1190_plain : CertifiedContract :=
  ⟨1190, 1191, 0, (.inc 2), s1190_plain_contract, 345, s1190_plain_checked⟩

def s1191_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1191_plain_checked : check 372 s1191_plain_contract = true := by decide +kernel
def s1191_plain : CertifiedContract :=
  ⟨1191, 1192, 0, (.inc 8), s1191_plain_contract, 372, s1191_plain_checked⟩

def s1192_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1192_plain_checked : check 97 s1192_plain_contract = true := by decide +kernel
def s1192_plain : CertifiedContract :=
  ⟨1192, 1189, 0, .none, s1192_plain_contract, 97, s1192_plain_checked⟩

def s1193_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1193_zero_checked : check 332 s1193_zero_contract = true := by decide +kernel
def s1193_zero : CertifiedContract :=
  ⟨1193, 1196, 0, .none, s1193_zero_contract, 332, s1193_zero_checked⟩

def s1193_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1193_positive_checked : check 332 s1193_positive_contract = true := by decide +kernel
def s1193_positive : CertifiedContract :=
  ⟨1193, 1194, 1, (.dec 8), s1193_positive_contract, 332, s1193_positive_checked⟩

def s1194_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s1194_plain_checked : check 336 s1194_plain_contract = true := by decide +kernel
def s1194_plain : CertifiedContract :=
  ⟨1194, 1195, 0, (.inc 4), s1194_plain_contract, 336, s1194_plain_checked⟩

def s1195_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1195_plain_checked : check 88 s1195_plain_contract = true := by decide +kernel
def s1195_plain : CertifiedContract :=
  ⟨1195, 1193, 0, .none, s1195_plain_contract, 88, s1195_plain_checked⟩

def s1196_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1196_zero_checked : check 326 s1196_zero_contract = true := by decide +kernel
def s1196_zero : CertifiedContract :=
  ⟨1196, 1199, 0, .none, s1196_zero_contract, 326, s1196_zero_checked⟩

def s1196_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1196_positive_checked : check 332 s1196_positive_contract = true := by decide +kernel
def s1196_positive : CertifiedContract :=
  ⟨1196, 1197, 1, (.dec 2), s1196_positive_contract, 332, s1196_positive_checked⟩

def s1197_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1197_plain_checked : check 345 s1197_plain_contract = true := by decide +kernel
def s1197_plain : CertifiedContract :=
  ⟨1197, 1198, 0, (.inc 8), s1197_plain_contract, 345, s1197_plain_checked⟩

def s1198_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1198_plain_checked : check 88 s1198_plain_contract = true := by decide +kernel
def s1198_plain : CertifiedContract :=
  ⟨1198, 1196, 0, .none, s1198_plain_contract, 88, s1198_plain_checked⟩

def s1199_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1199_zero_checked : check 347 s1199_zero_contract = true := by decide +kernel
def s1199_zero : CertifiedContract :=
  ⟨1199, 1202, 0, .none, s1199_zero_contract, 347, s1199_zero_checked⟩

def s1199_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1199_positive_checked : check 353 s1199_positive_contract = true := by decide +kernel
def s1199_positive : CertifiedContract :=
  ⟨1199, 1200, 1, (.dec 0), s1199_positive_contract, 353, s1199_positive_checked⟩

def s1200_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1200_plain_checked : check 345 s1200_plain_contract = true := by decide +kernel
def s1200_plain : CertifiedContract :=
  ⟨1200, 1201, 0, (.inc 2), s1200_plain_contract, 345, s1200_plain_checked⟩

def s1201_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1201_plain_checked : check 91 s1201_plain_contract = true := by decide +kernel
def s1201_plain : CertifiedContract :=
  ⟨1201, 1199, 0, .none, s1201_plain_contract, 91, s1201_plain_checked⟩

def s1202_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1202_zero_checked : check 353 s1202_zero_contract = true := by decide +kernel
def s1202_zero : CertifiedContract :=
  ⟨1202, 1206, 0, .none, s1202_zero_contract, 353, s1202_zero_checked⟩

def s1202_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1202_positive_checked : check 359 s1202_positive_contract = true := by decide +kernel
def s1202_positive : CertifiedContract :=
  ⟨1202, 1203, 1, (.dec 2), s1202_positive_contract, 359, s1202_positive_checked⟩

def s1203_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1203_plain_checked : check 372 s1203_plain_contract = true := by decide +kernel
def s1203_plain : CertifiedContract :=
  ⟨1203, 1204, 0, (.inc 5), s1203_plain_contract, 372, s1203_plain_checked⟩

def s1204_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1204_plain_checked : check 399 s1204_plain_contract = true := by decide +kernel
def s1204_plain : CertifiedContract :=
  ⟨1204, 1205, 0, (.inc 8), s1204_plain_contract, 399, s1204_plain_checked⟩

def s1205_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1205_plain_checked : check 106 s1205_plain_contract = true := by decide +kernel
def s1205_plain : CertifiedContract :=
  ⟨1205, 1202, 0, .none, s1205_plain_contract, 106, s1205_plain_checked⟩

def s1206_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1206_zero_checked : check 374 s1206_zero_contract = true := by decide +kernel
def s1206_zero : CertifiedContract :=
  ⟨1206, 1212, 0, .none, s1206_zero_contract, 374, s1206_zero_checked⟩

def s1206_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1206_positive_checked : check 377 s1206_positive_contract = true := by decide +kernel
def s1206_positive : CertifiedContract :=
  ⟨1206, 1207, 1, (.dec 8), s1206_positive_contract, 377, s1206_positive_checked⟩

def s1207_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1207_plain_checked : check 372 s1207_plain_contract = true := by decide +kernel
def s1207_plain : CertifiedContract :=
  ⟨1207, 1208, 0, (.inc 5), s1207_plain_contract, 372, s1207_plain_checked⟩

def s1208_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1208_zero_checked : check 392 s1208_zero_contract = true := by decide +kernel
def s1208_zero : CertifiedContract :=
  ⟨1208, 1211, 0, .none, s1208_zero_contract, 392, s1208_zero_checked⟩

def s1208_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1208_positive_checked : check 395 s1208_positive_contract = true := by decide +kernel
def s1208_positive : CertifiedContract :=
  ⟨1208, 1209, 1, (.dec 8), s1208_positive_contract, 395, s1208_positive_checked⟩

def s1209_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1209_plain_checked : check 390 s1209_plain_contract = true := by decide +kernel
def s1209_plain : CertifiedContract :=
  ⟨1209, 1210, 0, (.inc 2), s1209_plain_contract, 390, s1209_plain_checked⟩

def s1210_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1210_plain_checked : check 106 s1210_plain_contract = true := by decide +kernel
def s1210_plain : CertifiedContract :=
  ⟨1210, 1208, 0, .none, s1210_plain_contract, 106, s1210_plain_checked⟩

def s1211_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1211_plain_checked : check 109 s1211_plain_contract = true := by decide +kernel
def s1211_plain : CertifiedContract :=
  ⟨1211, 1202, 0, .none, s1211_plain_contract, 109, s1211_plain_checked⟩

def s1212_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1212_zero_checked : check 362 s1212_zero_contract = true := by decide +kernel
def s1212_zero : CertifiedContract :=
  ⟨1212, 1215, 0, .none, s1212_zero_contract, 362, s1212_zero_checked⟩

def s1212_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1212_positive_checked : check 359 s1212_positive_contract = true := by decide +kernel
def s1212_positive : CertifiedContract :=
  ⟨1212, 1213, 1, (.dec 5), s1212_positive_contract, 359, s1212_positive_checked⟩

def s1213_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1213_plain_checked : check 372 s1213_plain_contract = true := by decide +kernel
def s1213_plain : CertifiedContract :=
  ⟨1213, 1214, 0, (.inc 0), s1213_plain_contract, 372, s1213_plain_checked⟩

def s1214_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1214_plain_checked : check 97 s1214_plain_contract = true := by decide +kernel
def s1214_plain : CertifiedContract :=
  ⟨1214, 1212, 0, .none, s1214_plain_contract, 97, s1214_plain_checked⟩

def s1215_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1215_zero_checked : check 326 s1215_zero_contract = true := by decide +kernel
def s1215_zero : CertifiedContract :=
  ⟨1215, 1219, 0, .none, s1215_zero_contract, 326, s1215_zero_checked⟩

def s1215_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, false] 1 (.dec 3)⟩
theorem s1215_positive_checked : check 332 s1215_positive_contract = true := by decide +kernel
def s1215_positive : CertifiedContract :=
  ⟨1215, 1216, 1, (.dec 3), s1215_positive_contract, 332, s1215_positive_checked⟩

def s1216_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1216_plain_checked : check 345 s1216_plain_contract = true := by decide +kernel
def s1216_plain : CertifiedContract :=
  ⟨1216, 1217, 0, (.inc 2), s1216_plain_contract, 345, s1216_plain_checked⟩

def s1217_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1217_plain_checked : check 372 s1217_plain_contract = true := by decide +kernel
def s1217_plain : CertifiedContract :=
  ⟨1217, 1218, 0, (.inc 8), s1217_plain_contract, 372, s1217_plain_checked⟩

def s1218_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1218_plain_checked : check 97 s1218_plain_contract = true := by decide +kernel
def s1218_plain : CertifiedContract :=
  ⟨1218, 1215, 0, .none, s1218_plain_contract, 97, s1218_plain_checked⟩

def s1219_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1219_zero_checked : check 335 s1219_zero_contract = true := by decide +kernel
def s1219_zero : CertifiedContract :=
  ⟨1219, 1222, 0, .none, s1219_zero_contract, 335, s1219_zero_checked⟩

def s1219_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1219_positive_checked : check 332 s1219_positive_contract = true := by decide +kernel
def s1219_positive : CertifiedContract :=
  ⟨1219, 1220, 1, (.dec 8), s1219_positive_contract, 332, s1219_positive_checked⟩

def s1220_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, true] 0 (.inc 3)⟩
theorem s1220_plain_checked : check 348 s1220_plain_contract = true := by decide +kernel
def s1220_plain : CertifiedContract :=
  ⟨1220, 1221, 0, (.inc 3), s1220_plain_contract, 348, s1220_plain_checked⟩

def s1221_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1221_plain_checked : check 88 s1221_plain_contract = true := by decide +kernel
def s1221_plain : CertifiedContract :=
  ⟨1221, 1219, 0, .none, s1221_plain_contract, 88, s1221_plain_checked⟩

def s1222_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1222_zero_checked : check 338 s1222_zero_contract = true := by decide +kernel
def s1222_zero : CertifiedContract :=
  ⟨1222, 1230, 0, .none, s1222_zero_contract, 338, s1222_zero_checked⟩

def s1222_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1222_positive_checked : check 344 s1222_positive_contract = true := by decide +kernel
def s1222_positive : CertifiedContract :=
  ⟨1222, 1223, 1, (.dec 0), s1222_positive_contract, 344, s1222_positive_checked⟩

def s1223_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1223_plain_checked : check 354 s1223_plain_contract = true := by decide +kernel
def s1223_plain : CertifiedContract :=
  ⟨1223, 1224, 0, (.inc 5), s1223_plain_contract, 354, s1223_plain_checked⟩

def s1224_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1224_zero_checked : check 380 s1224_zero_contract = true := by decide +kernel
def s1224_zero : CertifiedContract :=
  ⟨1224, 1226, 0, .none, s1224_zero_contract, 380, s1224_zero_checked⟩

def s1224_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1224_positive_checked : check 386 s1224_positive_contract = true := by decide +kernel
def s1224_positive : CertifiedContract :=
  ⟨1224, 1225, 1, (.dec 8), s1224_positive_contract, 386, s1224_positive_checked⟩

def s1225_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1225_plain_checked : check 103 s1225_plain_contract = true := by decide +kernel
def s1225_plain : CertifiedContract :=
  ⟨1225, 1229, 0, .none, s1225_plain_contract, 103, s1225_plain_checked⟩

def s1226_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1226_zero_checked : check 392 s1226_zero_contract = true := by decide +kernel
def s1226_zero : CertifiedContract :=
  ⟨1226, 1229, 0, .none, s1226_zero_contract, 392, s1226_zero_checked⟩

def s1226_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1226_positive_checked : check 395 s1226_positive_contract = true := by decide +kernel
def s1226_positive : CertifiedContract :=
  ⟨1226, 1227, 1, (.dec 5), s1226_positive_contract, 395, s1226_positive_checked⟩

def s1227_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1227_plain_checked : check 399 s1227_plain_contract = true := by decide +kernel
def s1227_plain : CertifiedContract :=
  ⟨1227, 1228, 0, (.inc 8), s1227_plain_contract, 399, s1227_plain_checked⟩

def s1228_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1228_plain_checked : check 106 s1228_plain_contract = true := by decide +kernel
def s1228_plain : CertifiedContract :=
  ⟨1228, 1226, 0, .none, s1228_plain_contract, 106, s1228_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s1180_positive,
  s1181_plain,
  s1182_zero,
  s1182_positive,
  s1183_plain,
  s1184_plain,
  s1185_plain,
  s1186_zero,
  s1186_positive,
  s1187_plain,
  s1188_plain,
  s1189_zero,
  s1189_positive,
  s1190_plain,
  s1191_plain,
  s1192_plain,
  s1193_zero,
  s1193_positive,
  s1194_plain,
  s1195_plain,
  s1196_zero,
  s1196_positive,
  s1197_plain,
  s1198_plain,
  s1199_zero,
  s1199_positive,
  s1200_plain,
  s1201_plain,
  s1202_zero,
  s1202_positive,
  s1203_plain,
  s1204_plain,
  s1205_plain,
  s1206_zero,
  s1206_positive,
  s1207_plain,
  s1208_zero,
  s1208_positive,
  s1209_plain,
  s1210_plain,
  s1211_plain,
  s1212_zero,
  s1212_positive,
  s1213_plain,
  s1214_plain,
  s1215_zero,
  s1215_positive,
  s1216_plain,
  s1217_plain,
  s1218_plain,
  s1219_zero,
  s1219_positive,
  s1220_plain,
  s1221_plain,
  s1222_zero,
  s1222_positive,
  s1223_plain,
  s1224_zero,
  s1224_positive,
  s1225_plain,
  s1226_zero,
  s1226_positive,
  s1227_plain,
  s1228_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S024
