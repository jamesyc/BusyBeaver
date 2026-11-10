import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S027
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s1328_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1328_plain_checked : check 363 s1328_plain_contract = true := by decide +kernel
def s1328_plain : CertifiedContract :=
  ⟨1328, 1329, 0, (.inc 2), s1328_plain_contract, 363, s1328_plain_checked⟩

def s1329_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1329_plain_checked : check 369 s1329_plain_contract = true := by decide +kernel
def s1329_plain : CertifiedContract :=
  ⟨1329, 1330, 0, (.inc 2), s1329_plain_contract, 369, s1329_plain_checked⟩

def s1330_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s1330_plain_checked : check 91 s1330_plain_contract = true := by decide +kernel
def s1330_plain : CertifiedContract :=
  ⟨1330, 1325, 0, .none, s1330_plain_contract, 91, s1330_plain_checked⟩

def s1331_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s1331_plain_checked : check 333 s1331_plain_contract = true := by decide +kernel
def s1331_plain : CertifiedContract :=
  ⟨1331, 1332, 0, (.inc 2), s1331_plain_contract, 333, s1331_plain_checked⟩

def s1332_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1332_zero_checked : check 326 s1332_zero_contract = true := by decide +kernel
def s1332_zero : CertifiedContract :=
  ⟨1332, 1335, 0, .none, s1332_zero_contract, 326, s1332_zero_checked⟩

def s1332_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1332_positive_checked : check 332 s1332_positive_contract = true := by decide +kernel
def s1332_positive : CertifiedContract :=
  ⟨1332, 1333, 1, (.dec 2), s1332_positive_contract, 332, s1332_positive_checked⟩

def s1333_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1333_plain_checked : check 345 s1333_plain_contract = true := by decide +kernel
def s1333_plain : CertifiedContract :=
  ⟨1333, 1334, 0, (.inc 8), s1333_plain_contract, 345, s1333_plain_checked⟩

def s1334_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1334_plain_checked : check 88 s1334_plain_contract = true := by decide +kernel
def s1334_plain : CertifiedContract :=
  ⟨1334, 1332, 0, .none, s1334_plain_contract, 88, s1334_plain_checked⟩

def s1335_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1335_zero_checked : check 347 s1335_zero_contract = true := by decide +kernel
def s1335_zero : CertifiedContract :=
  ⟨1335, 1338, 0, .none, s1335_zero_contract, 347, s1335_zero_checked⟩

def s1335_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1335_positive_checked : check 353 s1335_positive_contract = true := by decide +kernel
def s1335_positive : CertifiedContract :=
  ⟨1335, 1336, 1, (.dec 0), s1335_positive_contract, 353, s1335_positive_checked⟩

def s1336_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1336_plain_checked : check 345 s1336_plain_contract = true := by decide +kernel
def s1336_plain : CertifiedContract :=
  ⟨1336, 1337, 0, (.inc 2), s1336_plain_contract, 345, s1336_plain_checked⟩

def s1337_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1337_plain_checked : check 91 s1337_plain_contract = true := by decide +kernel
def s1337_plain : CertifiedContract :=
  ⟨1337, 1335, 0, .none, s1337_plain_contract, 91, s1337_plain_checked⟩

def s1338_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1338_zero_checked : check 353 s1338_zero_contract = true := by decide +kernel
def s1338_zero : CertifiedContract :=
  ⟨1338, 1342, 0, .none, s1338_zero_contract, 353, s1338_zero_checked⟩

def s1338_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1338_positive_checked : check 359 s1338_positive_contract = true := by decide +kernel
def s1338_positive : CertifiedContract :=
  ⟨1338, 1339, 1, (.dec 2), s1338_positive_contract, 359, s1338_positive_checked⟩

def s1339_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1339_plain_checked : check 372 s1339_plain_contract = true := by decide +kernel
def s1339_plain : CertifiedContract :=
  ⟨1339, 1340, 0, (.inc 5), s1339_plain_contract, 372, s1339_plain_checked⟩

def s1340_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1340_plain_checked : check 399 s1340_plain_contract = true := by decide +kernel
def s1340_plain : CertifiedContract :=
  ⟨1340, 1341, 0, (.inc 8), s1340_plain_contract, 399, s1340_plain_checked⟩

def s1341_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1341_plain_checked : check 106 s1341_plain_contract = true := by decide +kernel
def s1341_plain : CertifiedContract :=
  ⟨1341, 1338, 0, .none, s1341_plain_contract, 106, s1341_plain_checked⟩

def s1342_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1342_zero_checked : check 374 s1342_zero_contract = true := by decide +kernel
def s1342_zero : CertifiedContract :=
  ⟨1342, 1348, 0, .none, s1342_zero_contract, 374, s1342_zero_checked⟩

def s1342_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1342_positive_checked : check 377 s1342_positive_contract = true := by decide +kernel
def s1342_positive : CertifiedContract :=
  ⟨1342, 1343, 1, (.dec 8), s1342_positive_contract, 377, s1342_positive_checked⟩

def s1343_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1343_plain_checked : check 372 s1343_plain_contract = true := by decide +kernel
def s1343_plain : CertifiedContract :=
  ⟨1343, 1344, 0, (.inc 5), s1343_plain_contract, 372, s1343_plain_checked⟩

def s1344_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1344_zero_checked : check 392 s1344_zero_contract = true := by decide +kernel
def s1344_zero : CertifiedContract :=
  ⟨1344, 1347, 0, .none, s1344_zero_contract, 392, s1344_zero_checked⟩

def s1344_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1344_positive_checked : check 395 s1344_positive_contract = true := by decide +kernel
def s1344_positive : CertifiedContract :=
  ⟨1344, 1345, 1, (.dec 8), s1344_positive_contract, 395, s1344_positive_checked⟩

def s1345_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1345_plain_checked : check 390 s1345_plain_contract = true := by decide +kernel
def s1345_plain : CertifiedContract :=
  ⟨1345, 1346, 0, (.inc 2), s1345_plain_contract, 390, s1345_plain_checked⟩

def s1346_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1346_plain_checked : check 106 s1346_plain_contract = true := by decide +kernel
def s1346_plain : CertifiedContract :=
  ⟨1346, 1344, 0, .none, s1346_plain_contract, 106, s1346_plain_checked⟩

def s1347_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1347_plain_checked : check 109 s1347_plain_contract = true := by decide +kernel
def s1347_plain : CertifiedContract :=
  ⟨1347, 1338, 0, .none, s1347_plain_contract, 109, s1347_plain_checked⟩

def s1348_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1348_zero_checked : check 362 s1348_zero_contract = true := by decide +kernel
def s1348_zero : CertifiedContract :=
  ⟨1348, 1351, 0, .none, s1348_zero_contract, 362, s1348_zero_checked⟩

def s1348_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1348_positive_checked : check 359 s1348_positive_contract = true := by decide +kernel
def s1348_positive : CertifiedContract :=
  ⟨1348, 1349, 1, (.dec 5), s1348_positive_contract, 359, s1348_positive_checked⟩

def s1349_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1349_plain_checked : check 372 s1349_plain_contract = true := by decide +kernel
def s1349_plain : CertifiedContract :=
  ⟨1349, 1350, 0, (.inc 0), s1349_plain_contract, 372, s1349_plain_checked⟩

def s1350_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1350_plain_checked : check 97 s1350_plain_contract = true := by decide +kernel
def s1350_plain : CertifiedContract :=
  ⟨1350, 1348, 0, .none, s1350_plain_contract, 97, s1350_plain_checked⟩

def s1351_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1351_zero_checked : check 326 s1351_zero_contract = true := by decide +kernel
def s1351_zero : CertifiedContract :=
  ⟨1351, 1355, 0, .none, s1351_zero_contract, 326, s1351_zero_checked⟩

def s1351_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s1351_positive_checked : check 332 s1351_positive_contract = true := by decide +kernel
def s1351_positive : CertifiedContract :=
  ⟨1351, 1352, 1, (.dec 3), s1351_positive_contract, 332, s1351_positive_checked⟩

def s1352_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1352_plain_checked : check 345 s1352_plain_contract = true := by decide +kernel
def s1352_plain : CertifiedContract :=
  ⟨1352, 1353, 0, (.inc 2), s1352_plain_contract, 345, s1352_plain_checked⟩

def s1353_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1353_plain_checked : check 372 s1353_plain_contract = true := by decide +kernel
def s1353_plain : CertifiedContract :=
  ⟨1353, 1354, 0, (.inc 8), s1353_plain_contract, 372, s1353_plain_checked⟩

def s1354_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1354_plain_checked : check 97 s1354_plain_contract = true := by decide +kernel
def s1354_plain : CertifiedContract :=
  ⟨1354, 1351, 0, .none, s1354_plain_contract, 97, s1354_plain_checked⟩

def s1355_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1355_zero_checked : check 332 s1355_zero_contract = true := by decide +kernel
def s1355_zero : CertifiedContract :=
  ⟨1355, 1358, 0, .none, s1355_zero_contract, 332, s1355_zero_checked⟩

def s1355_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1355_positive_checked : check 332 s1355_positive_contract = true := by decide +kernel
def s1355_positive : CertifiedContract :=
  ⟨1355, 1356, 1, (.dec 8), s1355_positive_contract, 332, s1355_positive_checked⟩

def s1356_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s1356_plain_checked : check 348 s1356_plain_contract = true := by decide +kernel
def s1356_plain : CertifiedContract :=
  ⟨1356, 1357, 0, (.inc 3), s1356_plain_contract, 348, s1356_plain_checked⟩

def s1357_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1357_plain_checked : check 88 s1357_plain_contract = true := by decide +kernel
def s1357_plain : CertifiedContract :=
  ⟨1357, 1355, 0, .none, s1357_plain_contract, 88, s1357_plain_checked⟩

def s1358_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1358_zero_checked : check 326 s1358_zero_contract = true := by decide +kernel
def s1358_zero : CertifiedContract :=
  ⟨1358, 1361, 0, .none, s1358_zero_contract, 326, s1358_zero_checked⟩

def s1358_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1358_positive_checked : check 332 s1358_positive_contract = true := by decide +kernel
def s1358_positive : CertifiedContract :=
  ⟨1358, 1359, 1, (.dec 2), s1358_positive_contract, 332, s1358_positive_checked⟩

def s1359_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1359_plain_checked : check 345 s1359_plain_contract = true := by decide +kernel
def s1359_plain : CertifiedContract :=
  ⟨1359, 1360, 0, (.inc 8), s1359_plain_contract, 345, s1359_plain_checked⟩

def s1360_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1360_plain_checked : check 88 s1360_plain_contract = true := by decide +kernel
def s1360_plain : CertifiedContract :=
  ⟨1360, 1358, 0, .none, s1360_plain_contract, 88, s1360_plain_checked⟩

def s1361_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1361_zero_checked : check 347 s1361_zero_contract = true := by decide +kernel
def s1361_zero : CertifiedContract :=
  ⟨1361, 1364, 0, .none, s1361_zero_contract, 347, s1361_zero_checked⟩

def s1361_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1361_positive_checked : check 353 s1361_positive_contract = true := by decide +kernel
def s1361_positive : CertifiedContract :=
  ⟨1361, 1362, 1, (.dec 0), s1361_positive_contract, 353, s1361_positive_checked⟩

def s1362_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1362_plain_checked : check 345 s1362_plain_contract = true := by decide +kernel
def s1362_plain : CertifiedContract :=
  ⟨1362, 1363, 0, (.inc 2), s1362_plain_contract, 345, s1362_plain_checked⟩

def s1363_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1363_plain_checked : check 91 s1363_plain_contract = true := by decide +kernel
def s1363_plain : CertifiedContract :=
  ⟨1363, 1361, 0, .none, s1363_plain_contract, 91, s1363_plain_checked⟩

def s1364_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1364_zero_checked : check 353 s1364_zero_contract = true := by decide +kernel
def s1364_zero : CertifiedContract :=
  ⟨1364, 1368, 0, .none, s1364_zero_contract, 353, s1364_zero_checked⟩

def s1364_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1364_positive_checked : check 359 s1364_positive_contract = true := by decide +kernel
def s1364_positive : CertifiedContract :=
  ⟨1364, 1365, 1, (.dec 2), s1364_positive_contract, 359, s1364_positive_checked⟩

def s1365_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1365_plain_checked : check 372 s1365_plain_contract = true := by decide +kernel
def s1365_plain : CertifiedContract :=
  ⟨1365, 1366, 0, (.inc 5), s1365_plain_contract, 372, s1365_plain_checked⟩

def s1366_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1366_plain_checked : check 399 s1366_plain_contract = true := by decide +kernel
def s1366_plain : CertifiedContract :=
  ⟨1366, 1367, 0, (.inc 8), s1366_plain_contract, 399, s1366_plain_checked⟩

def s1367_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1367_plain_checked : check 106 s1367_plain_contract = true := by decide +kernel
def s1367_plain : CertifiedContract :=
  ⟨1367, 1364, 0, .none, s1367_plain_contract, 106, s1367_plain_checked⟩

def s1368_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1368_zero_checked : check 374 s1368_zero_contract = true := by decide +kernel
def s1368_zero : CertifiedContract :=
  ⟨1368, 1374, 0, .none, s1368_zero_contract, 374, s1368_zero_checked⟩

def s1368_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1368_positive_checked : check 377 s1368_positive_contract = true := by decide +kernel
def s1368_positive : CertifiedContract :=
  ⟨1368, 1369, 1, (.dec 8), s1368_positive_contract, 377, s1368_positive_checked⟩

def s1369_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1369_plain_checked : check 372 s1369_plain_contract = true := by decide +kernel
def s1369_plain : CertifiedContract :=
  ⟨1369, 1370, 0, (.inc 5), s1369_plain_contract, 372, s1369_plain_checked⟩

def s1370_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1370_zero_checked : check 392 s1370_zero_contract = true := by decide +kernel
def s1370_zero : CertifiedContract :=
  ⟨1370, 1373, 0, .none, s1370_zero_contract, 392, s1370_zero_checked⟩

def s1370_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1370_positive_checked : check 395 s1370_positive_contract = true := by decide +kernel
def s1370_positive : CertifiedContract :=
  ⟨1370, 1371, 1, (.dec 8), s1370_positive_contract, 395, s1370_positive_checked⟩

def s1371_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1371_plain_checked : check 390 s1371_plain_contract = true := by decide +kernel
def s1371_plain : CertifiedContract :=
  ⟨1371, 1372, 0, (.inc 2), s1371_plain_contract, 390, s1371_plain_checked⟩

def s1372_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1372_plain_checked : check 106 s1372_plain_contract = true := by decide +kernel
def s1372_plain : CertifiedContract :=
  ⟨1372, 1370, 0, .none, s1372_plain_contract, 106, s1372_plain_checked⟩

def s1373_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1373_plain_checked : check 109 s1373_plain_contract = true := by decide +kernel
def s1373_plain : CertifiedContract :=
  ⟨1373, 1364, 0, .none, s1373_plain_contract, 109, s1373_plain_checked⟩

def s1374_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1374_zero_checked : check 362 s1374_zero_contract = true := by decide +kernel
def s1374_zero : CertifiedContract :=
  ⟨1374, 1377, 0, .none, s1374_zero_contract, 362, s1374_zero_checked⟩

def s1374_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1374_positive_checked : check 359 s1374_positive_contract = true := by decide +kernel
def s1374_positive : CertifiedContract :=
  ⟨1374, 1375, 1, (.dec 5), s1374_positive_contract, 359, s1374_positive_checked⟩

def s1375_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1375_plain_checked : check 372 s1375_plain_contract = true := by decide +kernel
def s1375_plain : CertifiedContract :=
  ⟨1375, 1376, 0, (.inc 0), s1375_plain_contract, 372, s1375_plain_checked⟩

def s1376_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1376_plain_checked : check 97 s1376_plain_contract = true := by decide +kernel
def s1376_plain : CertifiedContract :=
  ⟨1376, 1374, 0, .none, s1376_plain_contract, 97, s1376_plain_checked⟩

def s1377_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1377_zero_checked : check 326 s1377_zero_contract = true := by decide +kernel
def s1377_zero : CertifiedContract :=
  ⟨1377, 1381, 0, .none, s1377_zero_contract, 326, s1377_zero_checked⟩

def nonterminal : Array CertifiedContract := #[
  s1328_plain,
  s1329_plain,
  s1330_plain,
  s1331_plain,
  s1332_zero,
  s1332_positive,
  s1333_plain,
  s1334_plain,
  s1335_zero,
  s1335_positive,
  s1336_plain,
  s1337_plain,
  s1338_zero,
  s1338_positive,
  s1339_plain,
  s1340_plain,
  s1341_plain,
  s1342_zero,
  s1342_positive,
  s1343_plain,
  s1344_zero,
  s1344_positive,
  s1345_plain,
  s1346_plain,
  s1347_plain,
  s1348_zero,
  s1348_positive,
  s1349_plain,
  s1350_plain,
  s1351_zero,
  s1351_positive,
  s1352_plain,
  s1353_plain,
  s1354_plain,
  s1355_zero,
  s1355_positive,
  s1356_plain,
  s1357_plain,
  s1358_zero,
  s1358_positive,
  s1359_plain,
  s1360_plain,
  s1361_zero,
  s1361_positive,
  s1362_plain,
  s1363_plain,
  s1364_zero,
  s1364_positive,
  s1365_plain,
  s1366_plain,
  s1367_plain,
  s1368_zero,
  s1368_positive,
  s1369_plain,
  s1370_zero,
  s1370_positive,
  s1371_plain,
  s1372_plain,
  s1373_plain,
  s1374_zero,
  s1374_positive,
  s1375_plain,
  s1376_plain,
  s1377_zero
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S027
