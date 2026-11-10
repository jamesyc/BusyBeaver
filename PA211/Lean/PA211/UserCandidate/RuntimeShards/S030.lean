import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S030
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1476_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1476_positive_checked : check 387 s1476_positive_contract = true := by decide +kernel
def s1476_positive : CertifiedContract :=
  ⟨1476, 1477, 1, (.dec 8), s1476_positive_contract, 387, s1476_positive_checked⟩

def s1477_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1477_plain_checked : check 382 s1477_plain_contract = true := by decide +kernel
def s1477_plain : CertifiedContract :=
  ⟨1477, 1478, 0, (.inc 5), s1477_plain_contract, 382, s1477_plain_checked⟩

def s1478_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1478_zero_checked : check 402 s1478_zero_contract = true := by decide +kernel
def s1478_zero : CertifiedContract :=
  ⟨1478, 1481, 0, .none, s1478_zero_contract, 402, s1478_zero_checked⟩

def s1478_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1478_positive_checked : check 405 s1478_positive_contract = true := by decide +kernel
def s1478_positive : CertifiedContract :=
  ⟨1478, 1479, 1, (.dec 8), s1478_positive_contract, 405, s1478_positive_checked⟩

def s1479_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1479_plain_checked : check 400 s1479_plain_contract = true := by decide +kernel
def s1479_plain : CertifiedContract :=
  ⟨1479, 1480, 0, (.inc 2), s1479_plain_contract, 400, s1479_plain_checked⟩

def s1480_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1480_plain_checked : check 110 s1480_plain_contract = true := by decide +kernel
def s1480_plain : CertifiedContract :=
  ⟨1480, 1478, 0, .none, s1480_plain_contract, 110, s1480_plain_checked⟩

def s1481_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1481_plain_checked : check 113 s1481_plain_contract = true := by decide +kernel
def s1481_plain : CertifiedContract :=
  ⟨1481, 1472, 0, .none, s1481_plain_contract, 113, s1481_plain_checked⟩

def s1482_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s1482_zero_checked : check 372 s1482_zero_contract = true := by decide +kernel
def s1482_zero : CertifiedContract :=
  ⟨1482, 1485, 0, .none, s1482_zero_contract, 372, s1482_zero_checked⟩

def s1482_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1482_positive_checked : check 369 s1482_positive_contract = true := by decide +kernel
def s1482_positive : CertifiedContract :=
  ⟨1482, 1483, 1, (.dec 5), s1482_positive_contract, 369, s1482_positive_checked⟩

def s1483_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1483_plain_checked : check 382 s1483_plain_contract = true := by decide +kernel
def s1483_plain : CertifiedContract :=
  ⟨1483, 1484, 0, (.inc 0), s1483_plain_contract, 382, s1483_plain_checked⟩

def s1484_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s1484_plain_checked : check 101 s1484_plain_contract = true := by decide +kernel
def s1484_plain : CertifiedContract :=
  ⟨1484, 1482, 0, .none, s1484_plain_contract, 101, s1484_plain_checked⟩

def s1485_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s1485_zero_checked : check 336 s1485_zero_contract = true := by decide +kernel
def s1485_zero : CertifiedContract :=
  ⟨1485, 1489, 0, .none, s1485_zero_contract, 336, s1485_zero_checked⟩

def s1485_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, false] 1 (.dec 3)⟩
theorem s1485_positive_checked : check 342 s1485_positive_contract = true := by decide +kernel
def s1485_positive : CertifiedContract :=
  ⟨1485, 1486, 1, (.dec 3), s1485_positive_contract, 342, s1485_positive_checked⟩

def s1486_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1486_plain_checked : check 355 s1486_plain_contract = true := by decide +kernel
def s1486_plain : CertifiedContract :=
  ⟨1486, 1487, 0, (.inc 2), s1486_plain_contract, 355, s1486_plain_checked⟩

def s1487_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1487_plain_checked : check 382 s1487_plain_contract = true := by decide +kernel
def s1487_plain : CertifiedContract :=
  ⟨1487, 1488, 0, (.inc 8), s1487_plain_contract, 382, s1487_plain_checked⟩

def s1488_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s1488_plain_checked : check 101 s1488_plain_contract = true := by decide +kernel
def s1488_plain : CertifiedContract :=
  ⟨1488, 1485, 0, .none, s1488_plain_contract, 101, s1488_plain_checked⟩

def s1489_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s1489_zero_checked : check 345 s1489_zero_contract = true := by decide +kernel
def s1489_zero : CertifiedContract :=
  ⟨1489, 1492, 0, .none, s1489_zero_contract, 345, s1489_zero_checked⟩

def s1489_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1489_positive_checked : check 342 s1489_positive_contract = true := by decide +kernel
def s1489_positive : CertifiedContract :=
  ⟨1489, 1490, 1, (.dec 8), s1489_positive_contract, 342, s1489_positive_checked⟩

def s1490_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true, true, true] 0 (.inc 3)⟩
theorem s1490_plain_checked : check 358 s1490_plain_contract = true := by decide +kernel
def s1490_plain : CertifiedContract :=
  ⟨1490, 1491, 0, (.inc 3), s1490_plain_contract, 358, s1490_plain_checked⟩

def s1491_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s1491_plain_checked : check 92 s1491_plain_contract = true := by decide +kernel
def s1491_plain : CertifiedContract :=
  ⟨1491, 1489, 0, .none, s1491_plain_contract, 92, s1491_plain_checked⟩

def s1492_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s1492_zero_checked : check 327 s1492_zero_contract = true := by decide +kernel
def s1492_zero : CertifiedContract :=
  ⟨1492, 1495, 0, .none, s1492_zero_contract, 327, s1492_zero_checked⟩

def s1492_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1492_positive_checked : check 333 s1492_positive_contract = true := by decide +kernel
def s1492_positive : CertifiedContract :=
  ⟨1492, 1493, 1, (.dec 2), s1492_positive_contract, 333, s1492_positive_checked⟩

def s1493_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1493_plain_checked : check 346 s1493_plain_contract = true := by decide +kernel
def s1493_plain : CertifiedContract :=
  ⟨1493, 1494, 0, (.inc 8), s1493_plain_contract, 346, s1493_plain_checked⟩

def s1494_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s1494_plain_checked : check 89 s1494_plain_contract = true := by decide +kernel
def s1494_plain : CertifiedContract :=
  ⟨1494, 1492, 0, .none, s1494_plain_contract, 89, s1494_plain_checked⟩

def s1495_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s1495_zero_checked : check 348 s1495_zero_contract = true := by decide +kernel
def s1495_zero : CertifiedContract :=
  ⟨1495, 1498, 0, .none, s1495_zero_contract, 348, s1495_zero_checked⟩

def s1495_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1495_positive_checked : check 354 s1495_positive_contract = true := by decide +kernel
def s1495_positive : CertifiedContract :=
  ⟨1495, 1496, 1, (.dec 0), s1495_positive_contract, 354, s1495_positive_checked⟩

def s1496_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1496_plain_checked : check 346 s1496_plain_contract = true := by decide +kernel
def s1496_plain : CertifiedContract :=
  ⟨1496, 1497, 0, (.inc 2), s1496_plain_contract, 346, s1496_plain_checked⟩

def s1497_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s1497_plain_checked : check 92 s1497_plain_contract = true := by decide +kernel
def s1497_plain : CertifiedContract :=
  ⟨1497, 1495, 0, .none, s1497_plain_contract, 92, s1497_plain_checked⟩

def s1498_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1498_zero_checked : check 354 s1498_zero_contract = true := by decide +kernel
def s1498_zero : CertifiedContract :=
  ⟨1498, 1502, 0, .none, s1498_zero_contract, 354, s1498_zero_checked⟩

def s1498_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1498_positive_checked : check 360 s1498_positive_contract = true := by decide +kernel
def s1498_positive : CertifiedContract :=
  ⟨1498, 1499, 1, (.dec 2), s1498_positive_contract, 360, s1498_positive_checked⟩

def s1499_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1499_plain_checked : check 373 s1499_plain_contract = true := by decide +kernel
def s1499_plain : CertifiedContract :=
  ⟨1499, 1500, 0, (.inc 5), s1499_plain_contract, 373, s1499_plain_checked⟩

def s1500_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1500_plain_checked : check 400 s1500_plain_contract = true := by decide +kernel
def s1500_plain : CertifiedContract :=
  ⟨1500, 1501, 0, (.inc 8), s1500_plain_contract, 400, s1500_plain_checked⟩

def s1501_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s1501_plain_checked : check 107 s1501_plain_contract = true := by decide +kernel
def s1501_plain : CertifiedContract :=
  ⟨1501, 1498, 0, .none, s1501_plain_contract, 107, s1501_plain_checked⟩

def s1502_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s1502_zero_checked : check 375 s1502_zero_contract = true := by decide +kernel
def s1502_zero : CertifiedContract :=
  ⟨1502, 1508, 0, .none, s1502_zero_contract, 375, s1502_zero_checked⟩

def s1502_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1502_positive_checked : check 378 s1502_positive_contract = true := by decide +kernel
def s1502_positive : CertifiedContract :=
  ⟨1502, 1503, 1, (.dec 8), s1502_positive_contract, 378, s1502_positive_checked⟩

def s1503_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1503_plain_checked : check 373 s1503_plain_contract = true := by decide +kernel
def s1503_plain : CertifiedContract :=
  ⟨1503, 1504, 0, (.inc 5), s1503_plain_contract, 373, s1503_plain_checked⟩

def s1504_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1504_zero_checked : check 393 s1504_zero_contract = true := by decide +kernel
def s1504_zero : CertifiedContract :=
  ⟨1504, 1507, 0, .none, s1504_zero_contract, 393, s1504_zero_checked⟩

def s1504_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1504_positive_checked : check 396 s1504_positive_contract = true := by decide +kernel
def s1504_positive : CertifiedContract :=
  ⟨1504, 1505, 1, (.dec 8), s1504_positive_contract, 396, s1504_positive_checked⟩

def s1505_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1505_plain_checked : check 391 s1505_plain_contract = true := by decide +kernel
def s1505_plain : CertifiedContract :=
  ⟨1505, 1506, 0, (.inc 2), s1505_plain_contract, 391, s1505_plain_checked⟩

def s1506_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1506_plain_checked : check 107 s1506_plain_contract = true := by decide +kernel
def s1506_plain : CertifiedContract :=
  ⟨1506, 1504, 0, .none, s1506_plain_contract, 107, s1506_plain_checked⟩

def s1507_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s1507_plain_checked : check 110 s1507_plain_contract = true := by decide +kernel
def s1507_plain : CertifiedContract :=
  ⟨1507, 1498, 0, .none, s1507_plain_contract, 110, s1507_plain_checked⟩

def s1508_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false, false] 0 .none⟩
theorem s1508_zero_checked : check 363 s1508_zero_contract = true := by decide +kernel
def s1508_zero : CertifiedContract :=
  ⟨1508, 1511, 0, .none, s1508_zero_contract, 363, s1508_zero_checked⟩

def s1508_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1508_positive_checked : check 360 s1508_positive_contract = true := by decide +kernel
def s1508_positive : CertifiedContract :=
  ⟨1508, 1509, 1, (.dec 5), s1508_positive_contract, 360, s1508_positive_checked⟩

def s1509_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1509_plain_checked : check 373 s1509_plain_contract = true := by decide +kernel
def s1509_plain : CertifiedContract :=
  ⟨1509, 1510, 0, (.inc 0), s1509_plain_contract, 373, s1509_plain_checked⟩

def s1510_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s1510_plain_checked : check 98 s1510_plain_contract = true := by decide +kernel
def s1510_plain : CertifiedContract :=
  ⟨1510, 1508, 0, .none, s1510_plain_contract, 98, s1510_plain_checked⟩

def s1511_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s1511_zero_checked : check 327 s1511_zero_contract = true := by decide +kernel
def s1511_zero : CertifiedContract :=
  ⟨1511, 1515, 0, .none, s1511_zero_contract, 327, s1511_zero_checked⟩

def s1511_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false, true, false] 1 (.dec 7)⟩
theorem s1511_positive_checked : check 333 s1511_positive_contract = true := by decide +kernel
def s1511_positive : CertifiedContract :=
  ⟨1511, 1512, 1, (.dec 7), s1511_positive_contract, 333, s1511_positive_checked⟩

def s1512_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1512_plain_checked : check 337 s1512_plain_contract = true := by decide +kernel
def s1512_plain : CertifiedContract :=
  ⟨1512, 1513, 0, (.inc 2), s1512_plain_contract, 337, s1512_plain_checked⟩

def s1513_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1513_plain_checked : check 364 s1513_plain_contract = true := by decide +kernel
def s1513_plain : CertifiedContract :=
  ⟨1513, 1514, 0, (.inc 8), s1513_plain_contract, 364, s1513_plain_checked⟩

def s1514_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false, false] 0 .none⟩
theorem s1514_plain_checked : check 95 s1514_plain_contract = true := by decide +kernel
def s1514_plain : CertifiedContract :=
  ⟨1514, 1511, 0, .none, s1514_plain_contract, 95, s1514_plain_checked⟩

def s1515_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s1515_zero_checked : check 333 s1515_zero_contract = true := by decide +kernel
def s1515_zero : CertifiedContract :=
  ⟨1515, 1518, 0, .none, s1515_zero_contract, 333, s1515_zero_checked⟩

def s1515_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1515_positive_checked : check 333 s1515_positive_contract = true := by decide +kernel
def s1515_positive : CertifiedContract :=
  ⟨1515, 1516, 1, (.dec 8), s1515_positive_contract, 333, s1515_positive_checked⟩

def s1516_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true, true, true] 0 (.inc 7)⟩
theorem s1516_plain_checked : check 364 s1516_plain_contract = true := by decide +kernel
def s1516_plain : CertifiedContract :=
  ⟨1516, 1517, 0, (.inc 7), s1516_plain_contract, 364, s1516_plain_checked⟩

def s1517_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s1517_plain_checked : check 89 s1517_plain_contract = true := by decide +kernel
def s1517_plain : CertifiedContract :=
  ⟨1517, 1515, 0, .none, s1517_plain_contract, 89, s1517_plain_checked⟩

def s1518_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s1518_zero_checked : check 327 s1518_zero_contract = true := by decide +kernel
def s1518_zero : CertifiedContract :=
  ⟨1518, 1521, 0, .none, s1518_zero_contract, 327, s1518_zero_checked⟩

def s1518_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1518_positive_checked : check 333 s1518_positive_contract = true := by decide +kernel
def s1518_positive : CertifiedContract :=
  ⟨1518, 1519, 1, (.dec 2), s1518_positive_contract, 333, s1518_positive_checked⟩

def s1519_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1519_plain_checked : check 346 s1519_plain_contract = true := by decide +kernel
def s1519_plain : CertifiedContract :=
  ⟨1519, 1520, 0, (.inc 8), s1519_plain_contract, 346, s1519_plain_checked⟩

def s1520_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s1520_plain_checked : check 89 s1520_plain_contract = true := by decide +kernel
def s1520_plain : CertifiedContract :=
  ⟨1520, 1518, 0, .none, s1520_plain_contract, 89, s1520_plain_checked⟩

def s1521_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s1521_zero_checked : check 348 s1521_zero_contract = true := by decide +kernel
def s1521_zero : CertifiedContract :=
  ⟨1521, 1524, 0, .none, s1521_zero_contract, 348, s1521_zero_checked⟩

def s1521_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1521_positive_checked : check 354 s1521_positive_contract = true := by decide +kernel
def s1521_positive : CertifiedContract :=
  ⟨1521, 1522, 1, (.dec 0), s1521_positive_contract, 354, s1521_positive_checked⟩

def s1522_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1522_plain_checked : check 346 s1522_plain_contract = true := by decide +kernel
def s1522_plain : CertifiedContract :=
  ⟨1522, 1523, 0, (.inc 2), s1522_plain_contract, 346, s1522_plain_checked⟩

def s1523_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s1523_plain_checked : check 92 s1523_plain_contract = true := by decide +kernel
def s1523_plain : CertifiedContract :=
  ⟨1523, 1521, 0, .none, s1523_plain_contract, 92, s1523_plain_checked⟩

def s1524_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1524_zero_checked : check 354 s1524_zero_contract = true := by decide +kernel
def s1524_zero : CertifiedContract :=
  ⟨1524, 1528, 0, .none, s1524_zero_contract, 354, s1524_zero_checked⟩

def s1524_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1524_positive_checked : check 360 s1524_positive_contract = true := by decide +kernel
def s1524_positive : CertifiedContract :=
  ⟨1524, 1525, 1, (.dec 2), s1524_positive_contract, 360, s1524_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S030
