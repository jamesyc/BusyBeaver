import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S029
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s1427_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s1427_zero_checked : check 383 s1427_zero_contract = true := by decide +kernel
def s1427_zero : CertifiedContract :=
  ⟨1427, 1433, 0, .none, s1427_zero_contract, 383, s1427_zero_checked⟩

def s1427_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1427_positive_checked : check 386 s1427_positive_contract = true := by decide +kernel
def s1427_positive : CertifiedContract :=
  ⟨1427, 1428, 1, (.dec 8), s1427_positive_contract, 386, s1427_positive_checked⟩

def s1428_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1428_plain_checked : check 381 s1428_plain_contract = true := by decide +kernel
def s1428_plain : CertifiedContract :=
  ⟨1428, 1429, 0, (.inc 5), s1428_plain_contract, 381, s1428_plain_checked⟩

def s1429_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, true] 0 .none⟩
theorem s1429_zero_checked : check 401 s1429_zero_contract = true := by decide +kernel
def s1429_zero : CertifiedContract :=
  ⟨1429, 1432, 0, .none, s1429_zero_contract, 401, s1429_zero_checked⟩

def s1429_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1429_positive_checked : check 404 s1429_positive_contract = true := by decide +kernel
def s1429_positive : CertifiedContract :=
  ⟨1429, 1430, 1, (.dec 8), s1429_positive_contract, 404, s1429_positive_checked⟩

def s1430_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1430_plain_checked : check 399 s1430_plain_contract = true := by decide +kernel
def s1430_plain : CertifiedContract :=
  ⟨1430, 1431, 0, (.inc 2), s1430_plain_contract, 399, s1430_plain_checked⟩

def s1431_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1431_plain_checked : check 109 s1431_plain_contract = true := by decide +kernel
def s1431_plain : CertifiedContract :=
  ⟨1431, 1429, 0, .none, s1431_plain_contract, 109, s1431_plain_checked⟩

def s1432_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s1432_plain_checked : check 112 s1432_plain_contract = true := by decide +kernel
def s1432_plain : CertifiedContract :=
  ⟨1432, 1423, 0, .none, s1432_plain_contract, 112, s1432_plain_checked⟩

def s1433_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s1433_zero_checked : check 368 s1433_zero_contract = true := by decide +kernel
def s1433_zero : CertifiedContract :=
  ⟨1433, 1439, 0, .none, s1433_zero_contract, 368, s1433_zero_checked⟩

def s1433_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1433_positive_checked : check 368 s1433_positive_contract = true := by decide +kernel
def s1433_positive : CertifiedContract :=
  ⟨1433, 1434, 1, (.dec 5), s1433_positive_contract, 368, s1433_positive_checked⟩

def s1434_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1434_plain_checked : check 381 s1434_plain_contract = true := by decide +kernel
def s1434_plain : CertifiedContract :=
  ⟨1434, 1435, 0, (.inc 2), s1434_plain_contract, 381, s1434_plain_checked⟩

def s1435_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1435_plain_checked : check 384 s1435_plain_contract = true := by decide +kernel
def s1435_plain : CertifiedContract :=
  ⟨1435, 1436, 0, (.inc 2), s1435_plain_contract, 384, s1435_plain_checked⟩

def s1436_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1436_plain_checked : check 381 s1436_plain_contract = true := by decide +kernel
def s1436_plain : CertifiedContract :=
  ⟨1436, 1437, 0, (.inc 2), s1436_plain_contract, 381, s1436_plain_checked⟩

def s1437_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1437_plain_checked : check 387 s1437_plain_contract = true := by decide +kernel
def s1437_plain : CertifiedContract :=
  ⟨1437, 1438, 0, (.inc 2), s1437_plain_contract, 387, s1437_plain_checked⟩

def s1438_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s1438_plain_checked : check 97 s1438_plain_contract = true := by decide +kernel
def s1438_plain : CertifiedContract :=
  ⟨1438, 1433, 0, .none, s1438_plain_contract, 97, s1438_plain_checked⟩

def s1439_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s1439_zero_checked : check 374 s1439_zero_contract = true := by decide +kernel
def s1439_zero : CertifiedContract :=
  ⟨1439, 1447, 0, .none, s1439_zero_contract, 374, s1439_zero_checked⟩

def s1439_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, false] 1 (.dec 0)⟩
theorem s1439_positive_checked : check 380 s1439_positive_contract = true := by decide +kernel
def s1439_positive : CertifiedContract :=
  ⟨1439, 1440, 1, (.dec 0), s1439_positive_contract, 380, s1439_positive_checked⟩

def s1440_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1440_plain_checked : check 390 s1440_plain_contract = true := by decide +kernel
def s1440_plain : CertifiedContract :=
  ⟨1440, 1441, 0, (.inc 5), s1440_plain_contract, 390, s1440_plain_checked⟩

def s1441_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1441_zero_checked : check 416 s1441_zero_contract = true := by decide +kernel
def s1441_zero : CertifiedContract :=
  ⟨1441, 1443, 0, .none, s1441_zero_contract, 416, s1441_zero_checked⟩

def s1441_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1441_positive_checked : check 422 s1441_positive_contract = true := by decide +kernel
def s1441_positive : CertifiedContract :=
  ⟨1441, 1442, 1, (.dec 8), s1441_positive_contract, 422, s1441_positive_checked⟩

def s1442_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s1442_plain_checked : check 115 s1442_plain_contract = true := by decide +kernel
def s1442_plain : CertifiedContract :=
  ⟨1442, 1446, 0, .none, s1442_plain_contract, 115, s1442_plain_checked⟩

def s1443_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s1443_zero_checked : check 428 s1443_zero_contract = true := by decide +kernel
def s1443_zero : CertifiedContract :=
  ⟨1443, 1446, 0, .none, s1443_zero_contract, 428, s1443_zero_checked⟩

def s1443_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1443_positive_checked : check 431 s1443_positive_contract = true := by decide +kernel
def s1443_positive : CertifiedContract :=
  ⟨1443, 1444, 1, (.dec 5), s1443_positive_contract, 431, s1443_positive_checked⟩

def s1444_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1444_plain_checked : check 435 s1444_plain_contract = true := by decide +kernel
def s1444_plain : CertifiedContract :=
  ⟨1444, 1445, 0, (.inc 8), s1444_plain_contract, 435, s1444_plain_checked⟩

def s1445_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1445_plain_checked : check 118 s1445_plain_contract = true := by decide +kernel
def s1445_plain : CertifiedContract :=
  ⟨1445, 1443, 0, .none, s1445_plain_contract, 118, s1445_plain_checked⟩

def s1446_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s1446_plain_checked : check 109 s1446_plain_contract = true := by decide +kernel
def s1446_plain : CertifiedContract :=
  ⟨1446, 1439, 0, .none, s1446_plain_contract, 109, s1446_plain_checked⟩

def s1447_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s1447_zero_checked : check 374 s1447_zero_contract = true := by decide +kernel
def s1447_zero : CertifiedContract :=
  ⟨1447, 1450, 0, .none, s1447_zero_contract, 374, s1447_zero_checked⟩

def s1447_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1447_positive_checked : check 377 s1447_positive_contract = true := by decide +kernel
def s1447_positive : CertifiedContract :=
  ⟨1447, 1448, 1, (.dec 5), s1447_positive_contract, 377, s1447_positive_checked⟩

def s1448_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, true, true, true] 0 (.inc 0)⟩
theorem s1448_plain_checked : check 390 s1448_plain_contract = true := by decide +kernel
def s1448_plain : CertifiedContract :=
  ⟨1448, 1449, 0, (.inc 0), s1448_plain_contract, 390, s1448_plain_checked⟩

def s1449_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s1449_plain_checked : check 103 s1449_plain_contract = true := by decide +kernel
def s1449_plain : CertifiedContract :=
  ⟨1449, 1447, 0, .none, s1449_plain_contract, 103, s1449_plain_checked⟩

def s1450_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1450_zero_checked : check 371 s1450_zero_contract = true := by decide +kernel
def s1450_zero : CertifiedContract :=
  ⟨1450, 1454, 0, .none, s1450_zero_contract, 371, s1450_zero_checked⟩

def s1450_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1450_positive_checked : check 377 s1450_positive_contract = true := by decide +kernel
def s1450_positive : CertifiedContract :=
  ⟨1450, 1451, 1, (.dec 2), s1450_positive_contract, 377, s1450_positive_checked⟩

def s1451_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1451_plain_checked : check 390 s1451_plain_contract = true := by decide +kernel
def s1451_plain : CertifiedContract :=
  ⟨1451, 1452, 0, (.inc 5), s1451_plain_contract, 390, s1451_plain_checked⟩

def s1452_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1452_plain_checked : check 417 s1452_plain_contract = true := by decide +kernel
def s1452_plain : CertifiedContract :=
  ⟨1452, 1453, 0, (.inc 8), s1452_plain_contract, 417, s1452_plain_checked⟩

def s1453_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s1453_plain_checked : check 112 s1453_plain_contract = true := by decide +kernel
def s1453_plain : CertifiedContract :=
  ⟨1453, 1450, 0, .none, s1453_plain_contract, 112, s1453_plain_checked⟩

def s1454_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s1454_zero_checked : check 392 s1454_zero_contract = true := by decide +kernel
def s1454_zero : CertifiedContract :=
  ⟨1454, 1460, 0, .none, s1454_zero_contract, 392, s1454_zero_checked⟩

def s1454_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1454_positive_checked : check 395 s1454_positive_contract = true := by decide +kernel
def s1454_positive : CertifiedContract :=
  ⟨1454, 1455, 1, (.dec 8), s1454_positive_contract, 395, s1454_positive_checked⟩

def s1455_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1455_plain_checked : check 390 s1455_plain_contract = true := by decide +kernel
def s1455_plain : CertifiedContract :=
  ⟨1455, 1456, 0, (.inc 5), s1455_plain_contract, 390, s1455_plain_checked⟩

def s1456_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1456_zero_checked : check 410 s1456_zero_contract = true := by decide +kernel
def s1456_zero : CertifiedContract :=
  ⟨1456, 1459, 0, .none, s1456_zero_contract, 410, s1456_zero_checked⟩

def s1456_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1456_positive_checked : check 413 s1456_positive_contract = true := by decide +kernel
def s1456_positive : CertifiedContract :=
  ⟨1456, 1457, 1, (.dec 8), s1456_positive_contract, 413, s1456_positive_checked⟩

def s1457_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1457_plain_checked : check 408 s1457_plain_contract = true := by decide +kernel
def s1457_plain : CertifiedContract :=
  ⟨1457, 1458, 0, (.inc 2), s1457_plain_contract, 408, s1457_plain_checked⟩

def s1458_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1458_plain_checked : check 112 s1458_plain_contract = true := by decide +kernel
def s1458_plain : CertifiedContract :=
  ⟨1458, 1456, 0, .none, s1458_plain_contract, 112, s1458_plain_checked⟩

def s1459_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s1459_plain_checked : check 115 s1459_plain_contract = true := by decide +kernel
def s1459_plain : CertifiedContract :=
  ⟨1459, 1450, 0, .none, s1459_plain_contract, 115, s1459_plain_checked⟩

def s1460_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s1460_zero_checked : check 380 s1460_zero_contract = true := by decide +kernel
def s1460_zero : CertifiedContract :=
  ⟨1460, 1466, 0, .none, s1460_zero_contract, 380, s1460_zero_checked⟩

def s1460_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1460_positive_checked : check 377 s1460_positive_contract = true := by decide +kernel
def s1460_positive : CertifiedContract :=
  ⟨1460, 1461, 1, (.dec 5), s1460_positive_contract, 377, s1460_positive_checked⟩

def s1461_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1461_plain_checked : check 390 s1461_plain_contract = true := by decide +kernel
def s1461_plain : CertifiedContract :=
  ⟨1461, 1462, 0, (.inc 2), s1461_plain_contract, 390, s1461_plain_checked⟩

def s1462_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1462_plain_checked : check 393 s1462_plain_contract = true := by decide +kernel
def s1462_plain : CertifiedContract :=
  ⟨1462, 1463, 0, (.inc 2), s1462_plain_contract, 393, s1462_plain_checked⟩

def s1463_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1463_plain_checked : check 390 s1463_plain_contract = true := by decide +kernel
def s1463_plain : CertifiedContract :=
  ⟨1463, 1464, 0, (.inc 2), s1463_plain_contract, 390, s1463_plain_checked⟩

def s1464_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, true] 0 (.inc 2)⟩
theorem s1464_plain_checked : check 396 s1464_plain_contract = true := by decide +kernel
def s1464_plain : CertifiedContract :=
  ⟨1464, 1465, 0, (.inc 2), s1464_plain_contract, 396, s1464_plain_checked⟩

def s1465_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s1465_plain_checked : check 100 s1465_plain_contract = true := by decide +kernel
def s1465_plain : CertifiedContract :=
  ⟨1465, 1460, 0, .none, s1465_plain_contract, 100, s1465_plain_checked⟩

def s1466_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s1466_zero_checked : check 335 s1466_zero_contract = true := by decide +kernel
def s1466_zero : CertifiedContract :=
  ⟨1466, 1469, 0, .none, s1466_zero_contract, 335, s1466_zero_checked⟩

def s1466_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1466_positive_checked : check 341 s1466_positive_contract = true := by decide +kernel
def s1466_positive : CertifiedContract :=
  ⟨1466, 1467, 1, (.dec 2), s1466_positive_contract, 341, s1466_positive_checked⟩

def s1467_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1467_plain_checked : check 354 s1467_plain_contract = true := by decide +kernel
def s1467_plain : CertifiedContract :=
  ⟨1467, 1468, 0, (.inc 8), s1467_plain_contract, 354, s1467_plain_checked⟩

def s1468_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s1468_plain_checked : check 91 s1468_plain_contract = true := by decide +kernel
def s1468_plain : CertifiedContract :=
  ⟨1468, 1466, 0, .none, s1468_plain_contract, 91, s1468_plain_checked⟩

def s1469_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1469_zero_checked : check 356 s1469_zero_contract = true := by decide +kernel
def s1469_zero : CertifiedContract :=
  ⟨1469, 1472, 0, .none, s1469_zero_contract, 356, s1469_zero_checked⟩

def s1469_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1469_positive_checked : check 362 s1469_positive_contract = true := by decide +kernel
def s1469_positive : CertifiedContract :=
  ⟨1469, 1470, 1, (.dec 0), s1469_positive_contract, 362, s1469_positive_checked⟩

def s1470_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1470_plain_checked : check 354 s1470_plain_contract = true := by decide +kernel
def s1470_plain : CertifiedContract :=
  ⟨1470, 1471, 0, (.inc 2), s1470_plain_contract, 354, s1470_plain_checked⟩

def s1471_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s1471_plain_checked : check 94 s1471_plain_contract = true := by decide +kernel
def s1471_plain : CertifiedContract :=
  ⟨1471, 1469, 0, .none, s1471_plain_contract, 94, s1471_plain_checked⟩

def s1472_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1472_zero_checked : check 362 s1472_zero_contract = true := by decide +kernel
def s1472_zero : CertifiedContract :=
  ⟨1472, 1476, 0, .none, s1472_zero_contract, 362, s1472_zero_checked⟩

def s1472_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1472_positive_checked : check 368 s1472_positive_contract = true := by decide +kernel
def s1472_positive : CertifiedContract :=
  ⟨1472, 1473, 1, (.dec 2), s1472_positive_contract, 368, s1472_positive_checked⟩

def s1473_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1473_plain_checked : check 381 s1473_plain_contract = true := by decide +kernel
def s1473_plain : CertifiedContract :=
  ⟨1473, 1474, 0, (.inc 5), s1473_plain_contract, 381, s1473_plain_checked⟩

def s1474_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1474_plain_checked : check 408 s1474_plain_contract = true := by decide +kernel
def s1474_plain : CertifiedContract :=
  ⟨1474, 1475, 0, (.inc 8), s1474_plain_contract, 408, s1474_plain_checked⟩

def s1475_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1475_plain_checked : check 109 s1475_plain_contract = true := by decide +kernel
def s1475_plain : CertifiedContract :=
  ⟨1475, 1472, 0, .none, s1475_plain_contract, 109, s1475_plain_checked⟩

def s1476_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s1476_zero_checked : check 383 s1476_zero_contract = true := by decide +kernel
def s1476_zero : CertifiedContract :=
  ⟨1476, 1482, 0, .none, s1476_zero_contract, 383, s1476_zero_checked⟩

def nonterminal : Array CertifiedContract := #[
  s1427_zero,
  s1427_positive,
  s1428_plain,
  s1429_zero,
  s1429_positive,
  s1430_plain,
  s1431_plain,
  s1432_plain,
  s1433_zero,
  s1433_positive,
  s1434_plain,
  s1435_plain,
  s1436_plain,
  s1437_plain,
  s1438_plain,
  s1439_zero,
  s1439_positive,
  s1440_plain,
  s1441_zero,
  s1441_positive,
  s1442_plain,
  s1443_zero,
  s1443_positive,
  s1444_plain,
  s1445_plain,
  s1446_plain,
  s1447_zero,
  s1447_positive,
  s1448_plain,
  s1449_plain,
  s1450_zero,
  s1450_positive,
  s1451_plain,
  s1452_plain,
  s1453_plain,
  s1454_zero,
  s1454_positive,
  s1455_plain,
  s1456_zero,
  s1456_positive,
  s1457_plain,
  s1458_plain,
  s1459_plain,
  s1460_zero,
  s1460_positive,
  s1461_plain,
  s1462_plain,
  s1463_plain,
  s1464_plain,
  s1465_plain,
  s1466_zero,
  s1466_positive,
  s1467_plain,
  s1468_plain,
  s1469_zero,
  s1469_positive,
  s1470_plain,
  s1471_plain,
  s1472_zero,
  s1472_positive,
  s1473_plain,
  s1474_plain,
  s1475_plain,
  s1476_zero
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S029
