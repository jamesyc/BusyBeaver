module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S031
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s1525_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1525_plain_checked : check 372 s1525_plain_contract = true := by decide +kernel
def s1525_plain : CertifiedContract :=
  ⟨1525, 1526, 0, (.inc 5), s1525_plain_contract, 372, s1525_plain_checked⟩

def s1526_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1526_plain_checked : check 399 s1526_plain_contract = true := by decide +kernel
def s1526_plain : CertifiedContract :=
  ⟨1526, 1527, 0, (.inc 8), s1526_plain_contract, 399, s1526_plain_checked⟩

def s1527_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s1527_plain_checked : check 106 s1527_plain_contract = true := by decide +kernel
def s1527_plain : CertifiedContract :=
  ⟨1527, 1524, 0, .none, s1527_plain_contract, 106, s1527_plain_checked⟩

def s1528_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s1528_zero_checked : check 374 s1528_zero_contract = true := by decide +kernel
def s1528_zero : CertifiedContract :=
  ⟨1528, 1534, 0, .none, s1528_zero_contract, 374, s1528_zero_checked⟩

def s1528_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1528_positive_checked : check 377 s1528_positive_contract = true := by decide +kernel
def s1528_positive : CertifiedContract :=
  ⟨1528, 1529, 1, (.dec 8), s1528_positive_contract, 377, s1528_positive_checked⟩

def s1529_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1529_plain_checked : check 372 s1529_plain_contract = true := by decide +kernel
def s1529_plain : CertifiedContract :=
  ⟨1529, 1530, 0, (.inc 5), s1529_plain_contract, 372, s1529_plain_checked⟩

def s1530_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1530_zero_checked : check 392 s1530_zero_contract = true := by decide +kernel
def s1530_zero : CertifiedContract :=
  ⟨1530, 1533, 0, .none, s1530_zero_contract, 392, s1530_zero_checked⟩

def s1530_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1530_positive_checked : check 395 s1530_positive_contract = true := by decide +kernel
def s1530_positive : CertifiedContract :=
  ⟨1530, 1531, 1, (.dec 8), s1530_positive_contract, 395, s1530_positive_checked⟩

def s1531_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1531_plain_checked : check 390 s1531_plain_contract = true := by decide +kernel
def s1531_plain : CertifiedContract :=
  ⟨1531, 1532, 0, (.inc 2), s1531_plain_contract, 390, s1531_plain_checked⟩

def s1532_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1532_plain_checked : check 106 s1532_plain_contract = true := by decide +kernel
def s1532_plain : CertifiedContract :=
  ⟨1532, 1530, 0, .none, s1532_plain_contract, 106, s1532_plain_checked⟩

def s1533_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s1533_plain_checked : check 109 s1533_plain_contract = true := by decide +kernel
def s1533_plain : CertifiedContract :=
  ⟨1533, 1524, 0, .none, s1533_plain_contract, 109, s1533_plain_checked⟩

def s1534_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, false, false] 0 .none⟩
theorem s1534_zero_checked : check 362 s1534_zero_contract = true := by decide +kernel
def s1534_zero : CertifiedContract :=
  ⟨1534, 1537, 0, .none, s1534_zero_contract, 362, s1534_zero_checked⟩

def s1534_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1534_positive_checked : check 359 s1534_positive_contract = true := by decide +kernel
def s1534_positive : CertifiedContract :=
  ⟨1534, 1535, 1, (.dec 5), s1534_positive_contract, 359, s1534_positive_checked⟩

def s1535_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1535_plain_checked : check 372 s1535_plain_contract = true := by decide +kernel
def s1535_plain : CertifiedContract :=
  ⟨1535, 1536, 0, (.inc 0), s1535_plain_contract, 372, s1535_plain_checked⟩

def s1536_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s1536_plain_checked : check 97 s1536_plain_contract = true := by decide +kernel
def s1536_plain : CertifiedContract :=
  ⟨1536, 1534, 0, .none, s1536_plain_contract, 97, s1536_plain_checked⟩

def s1537_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s1537_zero_checked : check 326 s1537_zero_contract = true := by decide +kernel
def s1537_zero : CertifiedContract :=
  ⟨1537, 1541, 0, .none, s1537_zero_contract, 326, s1537_zero_checked⟩

def s1537_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, false, true, false] 1 (.dec 4)⟩
theorem s1537_positive_checked : check 332 s1537_positive_contract = true := by decide +kernel
def s1537_positive : CertifiedContract :=
  ⟨1537, 1538, 1, (.dec 4), s1537_positive_contract, 332, s1537_positive_checked⟩

def s1538_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1538_plain_checked : check 345 s1538_plain_contract = true := by decide +kernel
def s1538_plain : CertifiedContract :=
  ⟨1538, 1539, 0, (.inc 2), s1538_plain_contract, 345, s1538_plain_checked⟩

def s1539_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1539_plain_checked : check 372 s1539_plain_contract = true := by decide +kernel
def s1539_plain : CertifiedContract :=
  ⟨1539, 1540, 0, (.inc 8), s1539_plain_contract, 372, s1539_plain_checked⟩

def s1540_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, false, false] 0 .none⟩
theorem s1540_plain_checked : check 97 s1540_plain_contract = true := by decide +kernel
def s1540_plain : CertifiedContract :=
  ⟨1540, 1537, 0, .none, s1540_plain_contract, 97, s1540_plain_checked⟩

def s1541_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, false] 0 .none⟩
theorem s1541_zero_checked : check 344 s1541_zero_contract = true := by decide +kernel
def s1541_zero : CertifiedContract :=
  ⟨1541, 1544, 0, .none, s1541_zero_contract, 344, s1541_zero_checked⟩

def s1541_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1541_positive_checked : check 332 s1541_positive_contract = true := by decide +kernel
def s1541_positive : CertifiedContract :=
  ⟨1541, 1542, 1, (.dec 8), s1541_positive_contract, 332, s1541_positive_checked⟩

def s1542_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, true, true, true] 0 (.inc 4)⟩
theorem s1542_plain_checked : check 336 s1542_plain_contract = true := by decide +kernel
def s1542_plain : CertifiedContract :=
  ⟨1542, 1543, 0, (.inc 4), s1542_plain_contract, 336, s1542_plain_checked⟩

def s1543_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s1543_plain_checked : check 88 s1543_plain_contract = true := by decide +kernel
def s1543_plain : CertifiedContract :=
  ⟨1543, 1541, 0, .none, s1543_plain_contract, 88, s1543_plain_checked⟩

def s1544_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, true, false] 0 .none⟩
theorem s1544_zero_checked : check 311 s1544_zero_contract = true := by decide +kernel
def s1544_zero : CertifiedContract :=
  ⟨1544, 1552, 0, .none, s1544_zero_contract, 311, s1544_zero_checked⟩

def s1544_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1544_positive_checked : check 317 s1544_positive_contract = true := by decide +kernel
def s1544_positive : CertifiedContract :=
  ⟨1544, 1545, 1, (.dec 0), s1544_positive_contract, 317, s1544_positive_checked⟩

def s1545_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1545_plain_checked : check 327 s1545_plain_contract = true := by decide +kernel
def s1545_plain : CertifiedContract :=
  ⟨1545, 1546, 0, (.inc 5), s1545_plain_contract, 327, s1545_plain_checked⟩

def s1546_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1546_zero_checked : check 353 s1546_zero_contract = true := by decide +kernel
def s1546_zero : CertifiedContract :=
  ⟨1546, 1548, 0, .none, s1546_zero_contract, 353, s1546_zero_checked⟩

def s1546_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1546_positive_checked : check 359 s1546_positive_contract = true := by decide +kernel
def s1546_positive : CertifiedContract :=
  ⟨1546, 1547, 1, (.dec 8), s1546_positive_contract, 359, s1546_positive_checked⟩

def s1547_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s1547_plain_checked : check 94 s1547_plain_contract = true := by decide +kernel
def s1547_plain : CertifiedContract :=
  ⟨1547, 1551, 0, .none, s1547_plain_contract, 94, s1547_plain_checked⟩

def s1548_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s1548_zero_checked : check 365 s1548_zero_contract = true := by decide +kernel
def s1548_zero : CertifiedContract :=
  ⟨1548, 1551, 0, .none, s1548_zero_contract, 365, s1548_zero_checked⟩

def s1548_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1548_positive_checked : check 368 s1548_positive_contract = true := by decide +kernel
def s1548_positive : CertifiedContract :=
  ⟨1548, 1549, 1, (.dec 5), s1548_positive_contract, 368, s1548_positive_checked⟩

def s1549_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1549_plain_checked : check 372 s1549_plain_contract = true := by decide +kernel
def s1549_plain : CertifiedContract :=
  ⟨1549, 1550, 0, (.inc 8), s1549_plain_contract, 372, s1549_plain_checked⟩

def s1550_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1550_plain_checked : check 97 s1550_plain_contract = true := by decide +kernel
def s1550_plain : CertifiedContract :=
  ⟨1550, 1548, 0, .none, s1550_plain_contract, 97, s1550_plain_checked⟩

def s1551_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, false, false] 0 .none⟩
theorem s1551_plain_checked : check 88 s1551_plain_contract = true := by decide +kernel
def s1551_plain : CertifiedContract :=
  ⟨1551, 1544, 0, .none, s1551_plain_contract, 88, s1551_plain_checked⟩

def s1552_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s1552_zero_checked : check 311 s1552_zero_contract = true := by decide +kernel
def s1552_zero : CertifiedContract :=
  ⟨1552, 1555, 0, .none, s1552_zero_contract, 311, s1552_zero_checked⟩

def s1552_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1552_positive_checked : check 314 s1552_positive_contract = true := by decide +kernel
def s1552_positive : CertifiedContract :=
  ⟨1552, 1553, 1, (.dec 5), s1552_positive_contract, 314, s1552_positive_checked⟩

def s1553_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1553_plain_checked : check 327 s1553_plain_contract = true := by decide +kernel
def s1553_plain : CertifiedContract :=
  ⟨1553, 1554, 0, (.inc 0), s1553_plain_contract, 327, s1553_plain_checked⟩

def s1554_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, false, true, false] 0 .none⟩
theorem s1554_plain_checked : check 82 s1554_plain_contract = true := by decide +kernel
def s1554_plain : CertifiedContract :=
  ⟨1554, 1552, 0, .none, s1554_plain_contract, 82, s1554_plain_checked⟩

def s1555_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s1555_zero_checked : check 308 s1555_zero_contract = true := by decide +kernel
def s1555_zero : CertifiedContract :=
  ⟨1555, 1559, 0, .none, s1555_zero_contract, 308, s1555_zero_checked⟩

def s1555_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1555_positive_checked : check 314 s1555_positive_contract = true := by decide +kernel
def s1555_positive : CertifiedContract :=
  ⟨1555, 1556, 1, (.dec 2), s1555_positive_contract, 314, s1555_positive_checked⟩

def s1556_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1556_plain_checked : check 327 s1556_plain_contract = true := by decide +kernel
def s1556_plain : CertifiedContract :=
  ⟨1556, 1557, 0, (.inc 5), s1556_plain_contract, 327, s1556_plain_checked⟩

def s1557_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1557_plain_checked : check 354 s1557_plain_contract = true := by decide +kernel
def s1557_plain : CertifiedContract :=
  ⟨1557, 1558, 0, (.inc 8), s1557_plain_contract, 354, s1557_plain_checked⟩

def s1558_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s1558_plain_checked : check 91 s1558_plain_contract = true := by decide +kernel
def s1558_plain : CertifiedContract :=
  ⟨1558, 1555, 0, .none, s1558_plain_contract, 91, s1558_plain_checked⟩

def s1559_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, false] 0 .none⟩
theorem s1559_zero_checked : check 329 s1559_zero_contract = true := by decide +kernel
def s1559_zero : CertifiedContract :=
  ⟨1559, 1565, 0, .none, s1559_zero_contract, 329, s1559_zero_checked⟩

def s1559_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1559_positive_checked : check 332 s1559_positive_contract = true := by decide +kernel
def s1559_positive : CertifiedContract :=
  ⟨1559, 1560, 1, (.dec 8), s1559_positive_contract, 332, s1559_positive_checked⟩

def s1560_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1560_plain_checked : check 327 s1560_plain_contract = true := by decide +kernel
def s1560_plain : CertifiedContract :=
  ⟨1560, 1561, 0, (.inc 5), s1560_plain_contract, 327, s1560_plain_checked⟩

def s1561_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s1561_zero_checked : check 347 s1561_zero_contract = true := by decide +kernel
def s1561_zero : CertifiedContract :=
  ⟨1561, 1564, 0, .none, s1561_zero_contract, 347, s1561_zero_checked⟩

def s1561_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1561_positive_checked : check 350 s1561_positive_contract = true := by decide +kernel
def s1561_positive : CertifiedContract :=
  ⟨1561, 1562, 1, (.dec 8), s1561_positive_contract, 350, s1561_positive_checked⟩

def s1562_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1562_plain_checked : check 345 s1562_plain_contract = true := by decide +kernel
def s1562_plain : CertifiedContract :=
  ⟨1562, 1563, 0, (.inc 2), s1562_plain_contract, 345, s1562_plain_checked⟩

def s1563_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1563_plain_checked : check 91 s1563_plain_contract = true := by decide +kernel
def s1563_plain : CertifiedContract :=
  ⟨1563, 1561, 0, .none, s1563_plain_contract, 91, s1563_plain_checked⟩

def s1564_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s1564_plain_checked : check 94 s1564_plain_contract = true := by decide +kernel
def s1564_plain : CertifiedContract :=
  ⟨1564, 1555, 0, .none, s1564_plain_contract, 94, s1564_plain_checked⟩

def s1565_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1565_zero_checked : check 314 s1565_zero_contract = true := by decide +kernel
def s1565_zero : CertifiedContract :=
  ⟨1565, 1571, 0, .none, s1565_zero_contract, 314, s1565_zero_checked⟩

def s1565_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1565_positive_checked : check 314 s1565_positive_contract = true := by decide +kernel
def s1565_positive : CertifiedContract :=
  ⟨1565, 1566, 1, (.dec 5), s1565_positive_contract, 314, s1565_positive_checked⟩

def s1566_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1566_plain_checked : check 327 s1566_plain_contract = true := by decide +kernel
def s1566_plain : CertifiedContract :=
  ⟨1566, 1567, 0, (.inc 2), s1566_plain_contract, 327, s1566_plain_checked⟩

def s1567_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1567_plain_checked : check 330 s1567_plain_contract = true := by decide +kernel
def s1567_plain : CertifiedContract :=
  ⟨1567, 1568, 0, (.inc 2), s1567_plain_contract, 330, s1567_plain_checked⟩

def s1568_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1568_plain_checked : check 327 s1568_plain_contract = true := by decide +kernel
def s1568_plain : CertifiedContract :=
  ⟨1568, 1569, 0, (.inc 2), s1568_plain_contract, 327, s1568_plain_checked⟩

def s1569_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1569_plain_checked : check 333 s1569_plain_contract = true := by decide +kernel
def s1569_plain : CertifiedContract :=
  ⟨1569, 1570, 0, (.inc 2), s1569_plain_contract, 333, s1569_plain_checked⟩

def s1570_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, false, true, true, false] 0 .none⟩
theorem s1570_plain_checked : check 79 s1570_plain_contract = true := by decide +kernel
def s1570_plain : CertifiedContract :=
  ⟨1570, 1565, 0, .none, s1570_plain_contract, 79, s1570_plain_checked⟩

def s1571_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1571_plain_checked : check 282 s1571_plain_contract = true := by decide +kernel
def s1571_plain : CertifiedContract :=
  ⟨1571, 1572, 0, (.inc 2), s1571_plain_contract, 282, s1571_plain_checked⟩

def s1572_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, false] 0 (.inc 2)⟩
theorem s1572_plain_checked : check 288 s1572_plain_contract = true := by decide +kernel
def s1572_plain : CertifiedContract :=
  ⟨1572, 1573, 0, (.inc 2), s1572_plain_contract, 288, s1572_plain_checked⟩

def s1573_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, false] 0 .none⟩
theorem s1573_zero_checked : check 302 s1573_zero_contract = true := by decide +kernel
def s1573_zero : CertifiedContract :=
  ⟨1573, 1581, 0, .none, s1573_zero_contract, 302, s1573_zero_checked⟩

def s1573_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, false] 1 (.dec 0)⟩
theorem s1573_positive_checked : check 308 s1573_positive_contract = true := by decide +kernel
def s1573_positive : CertifiedContract :=
  ⟨1573, 1574, 1, (.dec 0), s1573_positive_contract, 308, s1573_positive_checked⟩

def s1574_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1574_plain_checked : check 318 s1574_plain_contract = true := by decide +kernel
def s1574_plain : CertifiedContract :=
  ⟨1574, 1575, 0, (.inc 5), s1574_plain_contract, 318, s1574_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s1525_plain,
  s1526_plain,
  s1527_plain,
  s1528_zero,
  s1528_positive,
  s1529_plain,
  s1530_zero,
  s1530_positive,
  s1531_plain,
  s1532_plain,
  s1533_plain,
  s1534_zero,
  s1534_positive,
  s1535_plain,
  s1536_plain,
  s1537_zero,
  s1537_positive,
  s1538_plain,
  s1539_plain,
  s1540_plain,
  s1541_zero,
  s1541_positive,
  s1542_plain,
  s1543_plain,
  s1544_zero,
  s1544_positive,
  s1545_plain,
  s1546_zero,
  s1546_positive,
  s1547_plain,
  s1548_zero,
  s1548_positive,
  s1549_plain,
  s1550_plain,
  s1551_plain,
  s1552_zero,
  s1552_positive,
  s1553_plain,
  s1554_plain,
  s1555_zero,
  s1555_positive,
  s1556_plain,
  s1557_plain,
  s1558_plain,
  s1559_zero,
  s1559_positive,
  s1560_plain,
  s1561_zero,
  s1561_positive,
  s1562_plain,
  s1563_plain,
  s1564_plain,
  s1565_zero,
  s1565_positive,
  s1566_plain,
  s1567_plain,
  s1568_plain,
  s1569_plain,
  s1570_plain,
  s1571_plain,
  s1572_plain,
  s1573_zero,
  s1573_positive,
  s1574_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S031
