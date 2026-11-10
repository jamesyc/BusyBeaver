import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S026
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s1279_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1279_plain_checked : check 354 s1279_plain_contract = true := by decide +kernel
def s1279_plain : CertifiedContract :=
  ⟨1279, 1280, 0, (.inc 8), s1279_plain_contract, 354, s1279_plain_checked⟩

def s1280_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s1280_plain_checked : check 91 s1280_plain_contract = true := by decide +kernel
def s1280_plain : CertifiedContract :=
  ⟨1280, 1278, 0, .none, s1280_plain_contract, 91, s1280_plain_checked⟩

def s1281_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1281_zero_checked : check 356 s1281_zero_contract = true := by decide +kernel
def s1281_zero : CertifiedContract :=
  ⟨1281, 1284, 0, .none, s1281_zero_contract, 356, s1281_zero_checked⟩

def s1281_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1281_positive_checked : check 362 s1281_positive_contract = true := by decide +kernel
def s1281_positive : CertifiedContract :=
  ⟨1281, 1282, 1, (.dec 0), s1281_positive_contract, 362, s1281_positive_checked⟩

def s1282_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1282_plain_checked : check 354 s1282_plain_contract = true := by decide +kernel
def s1282_plain : CertifiedContract :=
  ⟨1282, 1283, 0, (.inc 2), s1282_plain_contract, 354, s1282_plain_checked⟩

def s1283_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s1283_plain_checked : check 94 s1283_plain_contract = true := by decide +kernel
def s1283_plain : CertifiedContract :=
  ⟨1283, 1281, 0, .none, s1283_plain_contract, 94, s1283_plain_checked⟩

def s1284_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1284_zero_checked : check 362 s1284_zero_contract = true := by decide +kernel
def s1284_zero : CertifiedContract :=
  ⟨1284, 1288, 0, .none, s1284_zero_contract, 362, s1284_zero_checked⟩

def s1284_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1284_positive_checked : check 368 s1284_positive_contract = true := by decide +kernel
def s1284_positive : CertifiedContract :=
  ⟨1284, 1285, 1, (.dec 2), s1284_positive_contract, 368, s1284_positive_checked⟩

def s1285_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1285_plain_checked : check 381 s1285_plain_contract = true := by decide +kernel
def s1285_plain : CertifiedContract :=
  ⟨1285, 1286, 0, (.inc 5), s1285_plain_contract, 381, s1285_plain_checked⟩

def s1286_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1286_plain_checked : check 408 s1286_plain_contract = true := by decide +kernel
def s1286_plain : CertifiedContract :=
  ⟨1286, 1287, 0, (.inc 8), s1286_plain_contract, 408, s1286_plain_checked⟩

def s1287_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1287_plain_checked : check 109 s1287_plain_contract = true := by decide +kernel
def s1287_plain : CertifiedContract :=
  ⟨1287, 1284, 0, .none, s1287_plain_contract, 109, s1287_plain_checked⟩

def s1288_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s1288_zero_checked : check 383 s1288_zero_contract = true := by decide +kernel
def s1288_zero : CertifiedContract :=
  ⟨1288, 1294, 0, .none, s1288_zero_contract, 383, s1288_zero_checked⟩

def s1288_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1288_positive_checked : check 386 s1288_positive_contract = true := by decide +kernel
def s1288_positive : CertifiedContract :=
  ⟨1288, 1289, 1, (.dec 8), s1288_positive_contract, 386, s1288_positive_checked⟩

def s1289_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1289_plain_checked : check 381 s1289_plain_contract = true := by decide +kernel
def s1289_plain : CertifiedContract :=
  ⟨1289, 1290, 0, (.inc 5), s1289_plain_contract, 381, s1289_plain_checked⟩

def s1290_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1290_zero_checked : check 401 s1290_zero_contract = true := by decide +kernel
def s1290_zero : CertifiedContract :=
  ⟨1290, 1293, 0, .none, s1290_zero_contract, 401, s1290_zero_checked⟩

def s1290_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1290_positive_checked : check 404 s1290_positive_contract = true := by decide +kernel
def s1290_positive : CertifiedContract :=
  ⟨1290, 1291, 1, (.dec 8), s1290_positive_contract, 404, s1290_positive_checked⟩

def s1291_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1291_plain_checked : check 399 s1291_plain_contract = true := by decide +kernel
def s1291_plain : CertifiedContract :=
  ⟨1291, 1292, 0, (.inc 2), s1291_plain_contract, 399, s1291_plain_checked⟩

def s1292_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1292_plain_checked : check 109 s1292_plain_contract = true := by decide +kernel
def s1292_plain : CertifiedContract :=
  ⟨1292, 1290, 0, .none, s1292_plain_contract, 109, s1292_plain_checked⟩

def s1293_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1293_plain_checked : check 112 s1293_plain_contract = true := by decide +kernel
def s1293_plain : CertifiedContract :=
  ⟨1293, 1284, 0, .none, s1293_plain_contract, 112, s1293_plain_checked⟩

def s1294_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s1294_zero_checked : check 371 s1294_zero_contract = true := by decide +kernel
def s1294_zero : CertifiedContract :=
  ⟨1294, 1297, 0, .none, s1294_zero_contract, 371, s1294_zero_checked⟩

def s1294_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1294_positive_checked : check 368 s1294_positive_contract = true := by decide +kernel
def s1294_positive : CertifiedContract :=
  ⟨1294, 1295, 1, (.dec 5), s1294_positive_contract, 368, s1294_positive_checked⟩

def s1295_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1295_plain_checked : check 381 s1295_plain_contract = true := by decide +kernel
def s1295_plain : CertifiedContract :=
  ⟨1295, 1296, 0, (.inc 0), s1295_plain_contract, 381, s1295_plain_checked⟩

def s1296_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s1296_plain_checked : check 100 s1296_plain_contract = true := by decide +kernel
def s1296_plain : CertifiedContract :=
  ⟨1296, 1294, 0, .none, s1296_plain_contract, 100, s1296_plain_checked⟩

def s1297_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s1297_zero_checked : check 335 s1297_zero_contract = true := by decide +kernel
def s1297_zero : CertifiedContract :=
  ⟨1297, 1301, 0, .none, s1297_zero_contract, 335, s1297_zero_checked⟩

def s1297_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s1297_positive_checked : check 341 s1297_positive_contract = true := by decide +kernel
def s1297_positive : CertifiedContract :=
  ⟨1297, 1298, 1, (.dec 7), s1297_positive_contract, 341, s1297_positive_checked⟩

def s1298_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1298_plain_checked : check 345 s1298_plain_contract = true := by decide +kernel
def s1298_plain : CertifiedContract :=
  ⟨1298, 1299, 0, (.inc 2), s1298_plain_contract, 345, s1298_plain_checked⟩

def s1299_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1299_plain_checked : check 372 s1299_plain_contract = true := by decide +kernel
def s1299_plain : CertifiedContract :=
  ⟨1299, 1300, 0, (.inc 8), s1299_plain_contract, 372, s1299_plain_checked⟩

def s1300_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s1300_plain_checked : check 97 s1300_plain_contract = true := by decide +kernel
def s1300_plain : CertifiedContract :=
  ⟨1300, 1297, 0, .none, s1300_plain_contract, 97, s1300_plain_checked⟩

def s1301_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s1301_zero_checked : check 344 s1301_zero_contract = true := by decide +kernel
def s1301_zero : CertifiedContract :=
  ⟨1301, 1304, 0, .none, s1301_zero_contract, 344, s1301_zero_checked⟩

def s1301_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1301_positive_checked : check 341 s1301_positive_contract = true := by decide +kernel
def s1301_positive : CertifiedContract :=
  ⟨1301, 1302, 1, (.dec 8), s1301_positive_contract, 341, s1301_positive_checked⟩

def s1302_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s1302_plain_checked : check 372 s1302_plain_contract = true := by decide +kernel
def s1302_plain : CertifiedContract :=
  ⟨1302, 1303, 0, (.inc 7), s1302_plain_contract, 372, s1302_plain_checked⟩

def s1303_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s1303_plain_checked : check 91 s1303_plain_contract = true := by decide +kernel
def s1303_plain : CertifiedContract :=
  ⟨1303, 1301, 0, .none, s1303_plain_contract, 91, s1303_plain_checked⟩

def s1304_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s1304_zero_checked : check 347 s1304_zero_contract = true := by decide +kernel
def s1304_zero : CertifiedContract :=
  ⟨1304, 1312, 0, .none, s1304_zero_contract, 347, s1304_zero_checked⟩

def s1304_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1304_positive_checked : check 353 s1304_positive_contract = true := by decide +kernel
def s1304_positive : CertifiedContract :=
  ⟨1304, 1305, 1, (.dec 0), s1304_positive_contract, 353, s1304_positive_checked⟩

def s1305_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1305_plain_checked : check 363 s1305_plain_contract = true := by decide +kernel
def s1305_plain : CertifiedContract :=
  ⟨1305, 1306, 0, (.inc 5), s1305_plain_contract, 363, s1305_plain_checked⟩

def s1306_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1306_zero_checked : check 389 s1306_zero_contract = true := by decide +kernel
def s1306_zero : CertifiedContract :=
  ⟨1306, 1308, 0, .none, s1306_zero_contract, 389, s1306_zero_checked⟩

def s1306_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1306_positive_checked : check 395 s1306_positive_contract = true := by decide +kernel
def s1306_positive : CertifiedContract :=
  ⟨1306, 1307, 1, (.dec 8), s1306_positive_contract, 395, s1306_positive_checked⟩

def s1307_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s1307_plain_checked : check 106 s1307_plain_contract = true := by decide +kernel
def s1307_plain : CertifiedContract :=
  ⟨1307, 1311, 0, .none, s1307_plain_contract, 106, s1307_plain_checked⟩

def s1308_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s1308_zero_checked : check 401 s1308_zero_contract = true := by decide +kernel
def s1308_zero : CertifiedContract :=
  ⟨1308, 1311, 0, .none, s1308_zero_contract, 401, s1308_zero_checked⟩

def s1308_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1308_positive_checked : check 404 s1308_positive_contract = true := by decide +kernel
def s1308_positive : CertifiedContract :=
  ⟨1308, 1309, 1, (.dec 5), s1308_positive_contract, 404, s1308_positive_checked⟩

def s1309_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1309_plain_checked : check 408 s1309_plain_contract = true := by decide +kernel
def s1309_plain : CertifiedContract :=
  ⟨1309, 1310, 0, (.inc 8), s1309_plain_contract, 408, s1309_plain_checked⟩

def s1310_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1310_plain_checked : check 109 s1310_plain_contract = true := by decide +kernel
def s1310_plain : CertifiedContract :=
  ⟨1310, 1308, 0, .none, s1310_plain_contract, 109, s1310_plain_checked⟩

def s1311_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s1311_plain_checked : check 100 s1311_plain_contract = true := by decide +kernel
def s1311_plain : CertifiedContract :=
  ⟨1311, 1304, 0, .none, s1311_plain_contract, 100, s1311_plain_checked⟩

def s1312_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s1312_zero_checked : check 347 s1312_zero_contract = true := by decide +kernel
def s1312_zero : CertifiedContract :=
  ⟨1312, 1315, 0, .none, s1312_zero_contract, 347, s1312_zero_checked⟩

def s1312_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1312_positive_checked : check 350 s1312_positive_contract = true := by decide +kernel
def s1312_positive : CertifiedContract :=
  ⟨1312, 1313, 1, (.dec 5), s1312_positive_contract, 350, s1312_positive_checked⟩

def s1313_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1313_plain_checked : check 363 s1313_plain_contract = true := by decide +kernel
def s1313_plain : CertifiedContract :=
  ⟨1313, 1314, 0, (.inc 0), s1313_plain_contract, 363, s1313_plain_checked⟩

def s1314_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s1314_plain_checked : check 94 s1314_plain_contract = true := by decide +kernel
def s1314_plain : CertifiedContract :=
  ⟨1314, 1312, 0, .none, s1314_plain_contract, 94, s1314_plain_checked⟩

def s1315_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s1315_zero_checked : check 344 s1315_zero_contract = true := by decide +kernel
def s1315_zero : CertifiedContract :=
  ⟨1315, 1319, 0, .none, s1315_zero_contract, 344, s1315_zero_checked⟩

def s1315_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1315_positive_checked : check 350 s1315_positive_contract = true := by decide +kernel
def s1315_positive : CertifiedContract :=
  ⟨1315, 1316, 1, (.dec 2), s1315_positive_contract, 350, s1315_positive_checked⟩

def s1316_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1316_plain_checked : check 363 s1316_plain_contract = true := by decide +kernel
def s1316_plain : CertifiedContract :=
  ⟨1316, 1317, 0, (.inc 5), s1316_plain_contract, 363, s1316_plain_checked⟩

def s1317_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1317_plain_checked : check 390 s1317_plain_contract = true := by decide +kernel
def s1317_plain : CertifiedContract :=
  ⟨1317, 1318, 0, (.inc 8), s1317_plain_contract, 390, s1317_plain_checked⟩

def s1318_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s1318_plain_checked : check 103 s1318_plain_contract = true := by decide +kernel
def s1318_plain : CertifiedContract :=
  ⟨1318, 1315, 0, .none, s1318_plain_contract, 103, s1318_plain_checked⟩

def s1319_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s1319_zero_checked : check 365 s1319_zero_contract = true := by decide +kernel
def s1319_zero : CertifiedContract :=
  ⟨1319, 1325, 0, .none, s1319_zero_contract, 365, s1319_zero_checked⟩

def s1319_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1319_positive_checked : check 368 s1319_positive_contract = true := by decide +kernel
def s1319_positive : CertifiedContract :=
  ⟨1319, 1320, 1, (.dec 8), s1319_positive_contract, 368, s1319_positive_checked⟩

def s1320_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1320_plain_checked : check 363 s1320_plain_contract = true := by decide +kernel
def s1320_plain : CertifiedContract :=
  ⟨1320, 1321, 0, (.inc 5), s1320_plain_contract, 363, s1320_plain_checked⟩

def s1321_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s1321_zero_checked : check 383 s1321_zero_contract = true := by decide +kernel
def s1321_zero : CertifiedContract :=
  ⟨1321, 1324, 0, .none, s1321_zero_contract, 383, s1321_zero_checked⟩

def s1321_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1321_positive_checked : check 386 s1321_positive_contract = true := by decide +kernel
def s1321_positive : CertifiedContract :=
  ⟨1321, 1322, 1, (.dec 8), s1321_positive_contract, 386, s1321_positive_checked⟩

def s1322_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1322_plain_checked : check 381 s1322_plain_contract = true := by decide +kernel
def s1322_plain : CertifiedContract :=
  ⟨1322, 1323, 0, (.inc 2), s1322_plain_contract, 381, s1322_plain_checked⟩

def s1323_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1323_plain_checked : check 103 s1323_plain_contract = true := by decide +kernel
def s1323_plain : CertifiedContract :=
  ⟨1323, 1321, 0, .none, s1323_plain_contract, 103, s1323_plain_checked⟩

def s1324_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s1324_plain_checked : check 106 s1324_plain_contract = true := by decide +kernel
def s1324_plain : CertifiedContract :=
  ⟨1324, 1315, 0, .none, s1324_plain_contract, 106, s1324_plain_checked⟩

def s1325_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, true] 0 .none⟩
theorem s1325_zero_checked : check 350 s1325_zero_contract = true := by decide +kernel
def s1325_zero : CertifiedContract :=
  ⟨1325, 1331, 0, .none, s1325_zero_contract, 350, s1325_zero_checked⟩

def s1325_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1325_positive_checked : check 350 s1325_positive_contract = true := by decide +kernel
def s1325_positive : CertifiedContract :=
  ⟨1325, 1326, 1, (.dec 5), s1325_positive_contract, 350, s1325_positive_checked⟩

def s1326_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1326_plain_checked : check 363 s1326_plain_contract = true := by decide +kernel
def s1326_plain : CertifiedContract :=
  ⟨1326, 1327, 0, (.inc 2), s1326_plain_contract, 363, s1326_plain_checked⟩

def s1327_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1327_plain_checked : check 366 s1327_plain_contract = true := by decide +kernel
def s1327_plain : CertifiedContract :=
  ⟨1327, 1328, 0, (.inc 2), s1327_plain_contract, 366, s1327_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s1279_plain,
  s1280_plain,
  s1281_zero,
  s1281_positive,
  s1282_plain,
  s1283_plain,
  s1284_zero,
  s1284_positive,
  s1285_plain,
  s1286_plain,
  s1287_plain,
  s1288_zero,
  s1288_positive,
  s1289_plain,
  s1290_zero,
  s1290_positive,
  s1291_plain,
  s1292_plain,
  s1293_plain,
  s1294_zero,
  s1294_positive,
  s1295_plain,
  s1296_plain,
  s1297_zero,
  s1297_positive,
  s1298_plain,
  s1299_plain,
  s1300_plain,
  s1301_zero,
  s1301_positive,
  s1302_plain,
  s1303_plain,
  s1304_zero,
  s1304_positive,
  s1305_plain,
  s1306_zero,
  s1306_positive,
  s1307_plain,
  s1308_zero,
  s1308_positive,
  s1309_plain,
  s1310_plain,
  s1311_plain,
  s1312_zero,
  s1312_positive,
  s1313_plain,
  s1314_plain,
  s1315_zero,
  s1315_positive,
  s1316_plain,
  s1317_plain,
  s1318_plain,
  s1319_zero,
  s1319_positive,
  s1320_plain,
  s1321_zero,
  s1321_positive,
  s1322_plain,
  s1323_plain,
  s1324_plain,
  s1325_zero,
  s1325_positive,
  s1326_plain,
  s1327_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S026
