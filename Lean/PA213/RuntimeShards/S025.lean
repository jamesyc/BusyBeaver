import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S025
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s1229_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1229_plain_checked : check 97 s1229_plain_contract = true := by decide +kernel
def s1229_plain : CertifiedContract :=
  ⟨1229, 1222, 0, .none, s1229_plain_contract, 97, s1229_plain_checked⟩

def s1230_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1230_zero_checked : check 338 s1230_zero_contract = true := by decide +kernel
def s1230_zero : CertifiedContract :=
  ⟨1230, 1233, 0, .none, s1230_zero_contract, 338, s1230_zero_checked⟩

def s1230_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1230_positive_checked : check 341 s1230_positive_contract = true := by decide +kernel
def s1230_positive : CertifiedContract :=
  ⟨1230, 1231, 1, (.dec 5), s1230_positive_contract, 341, s1230_positive_checked⟩

def s1231_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1231_plain_checked : check 354 s1231_plain_contract = true := by decide +kernel
def s1231_plain : CertifiedContract :=
  ⟨1231, 1232, 0, (.inc 0), s1231_plain_contract, 354, s1231_plain_checked⟩

def s1232_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1232_plain_checked : check 91 s1232_plain_contract = true := by decide +kernel
def s1232_plain : CertifiedContract :=
  ⟨1232, 1230, 0, .none, s1232_plain_contract, 91, s1232_plain_checked⟩

def s1233_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s1233_zero_checked : check 335 s1233_zero_contract = true := by decide +kernel
def s1233_zero : CertifiedContract :=
  ⟨1233, 1237, 0, .none, s1233_zero_contract, 335, s1233_zero_checked⟩

def s1233_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1233_positive_checked : check 341 s1233_positive_contract = true := by decide +kernel
def s1233_positive : CertifiedContract :=
  ⟨1233, 1234, 1, (.dec 2), s1233_positive_contract, 341, s1233_positive_checked⟩

def s1234_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1234_plain_checked : check 354 s1234_plain_contract = true := by decide +kernel
def s1234_plain : CertifiedContract :=
  ⟨1234, 1235, 0, (.inc 5), s1234_plain_contract, 354, s1234_plain_checked⟩

def s1235_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1235_plain_checked : check 381 s1235_plain_contract = true := by decide +kernel
def s1235_plain : CertifiedContract :=
  ⟨1235, 1236, 0, (.inc 8), s1235_plain_contract, 381, s1235_plain_checked⟩

def s1236_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1236_plain_checked : check 100 s1236_plain_contract = true := by decide +kernel
def s1236_plain : CertifiedContract :=
  ⟨1236, 1233, 0, .none, s1236_plain_contract, 100, s1236_plain_checked⟩

def s1237_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1237_zero_checked : check 356 s1237_zero_contract = true := by decide +kernel
def s1237_zero : CertifiedContract :=
  ⟨1237, 1243, 0, .none, s1237_zero_contract, 356, s1237_zero_checked⟩

def s1237_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1237_positive_checked : check 359 s1237_positive_contract = true := by decide +kernel
def s1237_positive : CertifiedContract :=
  ⟨1237, 1238, 1, (.dec 8), s1237_positive_contract, 359, s1237_positive_checked⟩

def s1238_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1238_plain_checked : check 354 s1238_plain_contract = true := by decide +kernel
def s1238_plain : CertifiedContract :=
  ⟨1238, 1239, 0, (.inc 5), s1238_plain_contract, 354, s1238_plain_checked⟩

def s1239_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s1239_zero_checked : check 374 s1239_zero_contract = true := by decide +kernel
def s1239_zero : CertifiedContract :=
  ⟨1239, 1242, 0, .none, s1239_zero_contract, 374, s1239_zero_checked⟩

def s1239_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1239_positive_checked : check 377 s1239_positive_contract = true := by decide +kernel
def s1239_positive : CertifiedContract :=
  ⟨1239, 1240, 1, (.dec 8), s1239_positive_contract, 377, s1239_positive_checked⟩

def s1240_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1240_plain_checked : check 372 s1240_plain_contract = true := by decide +kernel
def s1240_plain : CertifiedContract :=
  ⟨1240, 1241, 0, (.inc 2), s1240_plain_contract, 372, s1240_plain_checked⟩

def s1241_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1241_plain_checked : check 100 s1241_plain_contract = true := by decide +kernel
def s1241_plain : CertifiedContract :=
  ⟨1241, 1239, 0, .none, s1241_plain_contract, 100, s1241_plain_checked⟩

def s1242_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1242_plain_checked : check 103 s1242_plain_contract = true := by decide +kernel
def s1242_plain : CertifiedContract :=
  ⟨1242, 1233, 0, .none, s1242_plain_contract, 103, s1242_plain_checked⟩

def s1243_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, true] 0 .none⟩
theorem s1243_zero_checked : check 341 s1243_zero_contract = true := by decide +kernel
def s1243_zero : CertifiedContract :=
  ⟨1243, 1249, 0, .none, s1243_zero_contract, 341, s1243_zero_checked⟩

def s1243_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1243_positive_checked : check 341 s1243_positive_contract = true := by decide +kernel
def s1243_positive : CertifiedContract :=
  ⟨1243, 1244, 1, (.dec 5), s1243_positive_contract, 341, s1243_positive_checked⟩

def s1244_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1244_plain_checked : check 354 s1244_plain_contract = true := by decide +kernel
def s1244_plain : CertifiedContract :=
  ⟨1244, 1245, 0, (.inc 2), s1244_plain_contract, 354, s1244_plain_checked⟩

def s1245_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1245_plain_checked : check 357 s1245_plain_contract = true := by decide +kernel
def s1245_plain : CertifiedContract :=
  ⟨1245, 1246, 0, (.inc 2), s1245_plain_contract, 357, s1245_plain_checked⟩

def s1246_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1246_plain_checked : check 354 s1246_plain_contract = true := by decide +kernel
def s1246_plain : CertifiedContract :=
  ⟨1246, 1247, 0, (.inc 2), s1246_plain_contract, 354, s1246_plain_checked⟩

def s1247_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1247_plain_checked : check 360 s1247_plain_contract = true := by decide +kernel
def s1247_plain : CertifiedContract :=
  ⟨1247, 1248, 0, (.inc 2), s1247_plain_contract, 360, s1247_plain_checked⟩

def s1248_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1248_plain_checked : check 88 s1248_plain_contract = true := by decide +kernel
def s1248_plain : CertifiedContract :=
  ⟨1248, 1243, 0, .none, s1248_plain_contract, 88, s1248_plain_checked⟩

def s1249_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, false, false] 0 (.inc 2)⟩
theorem s1249_plain_checked : check 315 s1249_plain_contract = true := by decide +kernel
def s1249_plain : CertifiedContract :=
  ⟨1249, 1250, 0, (.inc 2), s1249_plain_contract, 315, s1249_plain_checked⟩

def s1250_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, false, true] 0 (.inc 2)⟩
theorem s1250_plain_checked : check 300 s1250_plain_contract = true := by decide +kernel
def s1250_plain : CertifiedContract :=
  ⟨1250, 1251, 0, (.inc 2), s1250_plain_contract, 300, s1250_plain_checked⟩

def s1251_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s1251_plain_checked : check 303 s1251_plain_contract = true := by decide +kernel
def s1251_plain : CertifiedContract :=
  ⟨1251, 1252, 0, (.inc 2), s1251_plain_contract, 303, s1251_plain_checked⟩

def s1252_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s1252_zero_checked : check 335 s1252_zero_contract = true := by decide +kernel
def s1252_zero : CertifiedContract :=
  ⟨1252, 1255, 0, .none, s1252_zero_contract, 335, s1252_zero_checked⟩

def s1252_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1252_positive_checked : check 341 s1252_positive_contract = true := by decide +kernel
def s1252_positive : CertifiedContract :=
  ⟨1252, 1253, 1, (.dec 2), s1252_positive_contract, 341, s1252_positive_checked⟩

def s1253_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1253_plain_checked : check 354 s1253_plain_contract = true := by decide +kernel
def s1253_plain : CertifiedContract :=
  ⟨1253, 1254, 0, (.inc 8), s1253_plain_contract, 354, s1253_plain_checked⟩

def s1254_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s1254_plain_checked : check 91 s1254_plain_contract = true := by decide +kernel
def s1254_plain : CertifiedContract :=
  ⟨1254, 1252, 0, .none, s1254_plain_contract, 91, s1254_plain_checked⟩

def s1255_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1255_zero_checked : check 356 s1255_zero_contract = true := by decide +kernel
def s1255_zero : CertifiedContract :=
  ⟨1255, 1258, 0, .none, s1255_zero_contract, 356, s1255_zero_checked⟩

def s1255_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1255_positive_checked : check 362 s1255_positive_contract = true := by decide +kernel
def s1255_positive : CertifiedContract :=
  ⟨1255, 1256, 1, (.dec 0), s1255_positive_contract, 362, s1255_positive_checked⟩

def s1256_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1256_plain_checked : check 354 s1256_plain_contract = true := by decide +kernel
def s1256_plain : CertifiedContract :=
  ⟨1256, 1257, 0, (.inc 2), s1256_plain_contract, 354, s1256_plain_checked⟩

def s1257_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s1257_plain_checked : check 94 s1257_plain_contract = true := by decide +kernel
def s1257_plain : CertifiedContract :=
  ⟨1257, 1255, 0, .none, s1257_plain_contract, 94, s1257_plain_checked⟩

def s1258_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1258_zero_checked : check 362 s1258_zero_contract = true := by decide +kernel
def s1258_zero : CertifiedContract :=
  ⟨1258, 1262, 0, .none, s1258_zero_contract, 362, s1258_zero_checked⟩

def s1258_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1258_positive_checked : check 368 s1258_positive_contract = true := by decide +kernel
def s1258_positive : CertifiedContract :=
  ⟨1258, 1259, 1, (.dec 2), s1258_positive_contract, 368, s1258_positive_checked⟩

def s1259_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1259_plain_checked : check 381 s1259_plain_contract = true := by decide +kernel
def s1259_plain : CertifiedContract :=
  ⟨1259, 1260, 0, (.inc 5), s1259_plain_contract, 381, s1259_plain_checked⟩

def s1260_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1260_plain_checked : check 408 s1260_plain_contract = true := by decide +kernel
def s1260_plain : CertifiedContract :=
  ⟨1260, 1261, 0, (.inc 8), s1260_plain_contract, 408, s1260_plain_checked⟩

def s1261_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1261_plain_checked : check 109 s1261_plain_contract = true := by decide +kernel
def s1261_plain : CertifiedContract :=
  ⟨1261, 1258, 0, .none, s1261_plain_contract, 109, s1261_plain_checked⟩

def s1262_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s1262_zero_checked : check 383 s1262_zero_contract = true := by decide +kernel
def s1262_zero : CertifiedContract :=
  ⟨1262, 1268, 0, .none, s1262_zero_contract, 383, s1262_zero_checked⟩

def s1262_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1262_positive_checked : check 386 s1262_positive_contract = true := by decide +kernel
def s1262_positive : CertifiedContract :=
  ⟨1262, 1263, 1, (.dec 8), s1262_positive_contract, 386, s1262_positive_checked⟩

def s1263_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1263_plain_checked : check 381 s1263_plain_contract = true := by decide +kernel
def s1263_plain : CertifiedContract :=
  ⟨1263, 1264, 0, (.inc 5), s1263_plain_contract, 381, s1263_plain_checked⟩

def s1264_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1264_zero_checked : check 401 s1264_zero_contract = true := by decide +kernel
def s1264_zero : CertifiedContract :=
  ⟨1264, 1267, 0, .none, s1264_zero_contract, 401, s1264_zero_checked⟩

def s1264_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1264_positive_checked : check 404 s1264_positive_contract = true := by decide +kernel
def s1264_positive : CertifiedContract :=
  ⟨1264, 1265, 1, (.dec 8), s1264_positive_contract, 404, s1264_positive_checked⟩

def s1265_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1265_plain_checked : check 399 s1265_plain_contract = true := by decide +kernel
def s1265_plain : CertifiedContract :=
  ⟨1265, 1266, 0, (.inc 2), s1265_plain_contract, 399, s1265_plain_checked⟩

def s1266_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1266_plain_checked : check 109 s1266_plain_contract = true := by decide +kernel
def s1266_plain : CertifiedContract :=
  ⟨1266, 1264, 0, .none, s1266_plain_contract, 109, s1266_plain_checked⟩

def s1267_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1267_plain_checked : check 112 s1267_plain_contract = true := by decide +kernel
def s1267_plain : CertifiedContract :=
  ⟨1267, 1258, 0, .none, s1267_plain_contract, 112, s1267_plain_checked⟩

def s1268_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s1268_zero_checked : check 371 s1268_zero_contract = true := by decide +kernel
def s1268_zero : CertifiedContract :=
  ⟨1268, 1271, 0, .none, s1268_zero_contract, 371, s1268_zero_checked⟩

def s1268_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1268_positive_checked : check 368 s1268_positive_contract = true := by decide +kernel
def s1268_positive : CertifiedContract :=
  ⟨1268, 1269, 1, (.dec 5), s1268_positive_contract, 368, s1268_positive_checked⟩

def s1269_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1269_plain_checked : check 381 s1269_plain_contract = true := by decide +kernel
def s1269_plain : CertifiedContract :=
  ⟨1269, 1270, 0, (.inc 0), s1269_plain_contract, 381, s1269_plain_checked⟩

def s1270_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s1270_plain_checked : check 100 s1270_plain_contract = true := by decide +kernel
def s1270_plain : CertifiedContract :=
  ⟨1270, 1268, 0, .none, s1270_plain_contract, 100, s1270_plain_checked⟩

def s1271_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s1271_zero_checked : check 335 s1271_zero_contract = true := by decide +kernel
def s1271_zero : CertifiedContract :=
  ⟨1271, 1275, 0, .none, s1271_zero_contract, 335, s1271_zero_checked⟩

def s1271_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s1271_positive_checked : check 341 s1271_positive_contract = true := by decide +kernel
def s1271_positive : CertifiedContract :=
  ⟨1271, 1272, 1, (.dec 4), s1271_positive_contract, 341, s1271_positive_checked⟩

def s1272_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1272_plain_checked : check 354 s1272_plain_contract = true := by decide +kernel
def s1272_plain : CertifiedContract :=
  ⟨1272, 1273, 0, (.inc 2), s1272_plain_contract, 354, s1272_plain_checked⟩

def s1273_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1273_plain_checked : check 381 s1273_plain_contract = true := by decide +kernel
def s1273_plain : CertifiedContract :=
  ⟨1273, 1274, 0, (.inc 8), s1273_plain_contract, 381, s1273_plain_checked⟩

def s1274_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s1274_plain_checked : check 100 s1274_plain_contract = true := by decide +kernel
def s1274_plain : CertifiedContract :=
  ⟨1274, 1271, 0, .none, s1274_plain_contract, 100, s1274_plain_checked⟩

def s1275_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s1275_zero_checked : check 341 s1275_zero_contract = true := by decide +kernel
def s1275_zero : CertifiedContract :=
  ⟨1275, 1278, 0, .none, s1275_zero_contract, 341, s1275_zero_checked⟩

def s1275_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1275_positive_checked : check 341 s1275_positive_contract = true := by decide +kernel
def s1275_positive : CertifiedContract :=
  ⟨1275, 1276, 1, (.dec 8), s1275_positive_contract, 341, s1275_positive_checked⟩

def s1276_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s1276_plain_checked : check 345 s1276_plain_contract = true := by decide +kernel
def s1276_plain : CertifiedContract :=
  ⟨1276, 1277, 0, (.inc 4), s1276_plain_contract, 345, s1276_plain_checked⟩

def s1277_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s1277_plain_checked : check 91 s1277_plain_contract = true := by decide +kernel
def s1277_plain : CertifiedContract :=
  ⟨1277, 1275, 0, .none, s1277_plain_contract, 91, s1277_plain_checked⟩

def s1278_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s1278_zero_checked : check 335 s1278_zero_contract = true := by decide +kernel
def s1278_zero : CertifiedContract :=
  ⟨1278, 1281, 0, .none, s1278_zero_contract, 335, s1278_zero_checked⟩

def s1278_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1278_positive_checked : check 341 s1278_positive_contract = true := by decide +kernel
def s1278_positive : CertifiedContract :=
  ⟨1278, 1279, 1, (.dec 2), s1278_positive_contract, 341, s1278_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s1229_plain,
  s1230_zero,
  s1230_positive,
  s1231_plain,
  s1232_plain,
  s1233_zero,
  s1233_positive,
  s1234_plain,
  s1235_plain,
  s1236_plain,
  s1237_zero,
  s1237_positive,
  s1238_plain,
  s1239_zero,
  s1239_positive,
  s1240_plain,
  s1241_plain,
  s1242_plain,
  s1243_zero,
  s1243_positive,
  s1244_plain,
  s1245_plain,
  s1246_plain,
  s1247_plain,
  s1248_plain,
  s1249_plain,
  s1250_plain,
  s1251_plain,
  s1252_zero,
  s1252_positive,
  s1253_plain,
  s1254_plain,
  s1255_zero,
  s1255_positive,
  s1256_plain,
  s1257_plain,
  s1258_zero,
  s1258_positive,
  s1259_plain,
  s1260_plain,
  s1261_plain,
  s1262_zero,
  s1262_positive,
  s1263_plain,
  s1264_zero,
  s1264_positive,
  s1265_plain,
  s1266_plain,
  s1267_plain,
  s1268_zero,
  s1268_positive,
  s1269_plain,
  s1270_plain,
  s1271_zero,
  s1271_positive,
  s1272_plain,
  s1273_plain,
  s1274_plain,
  s1275_zero,
  s1275_positive,
  s1276_plain,
  s1277_plain,
  s1278_zero,
  s1278_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S025
