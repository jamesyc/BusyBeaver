import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S033
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s1625_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1625_zero_checked : check 341 s1625_zero_contract = true := by decide +kernel
def s1625_zero : CertifiedContract :=
  ⟨1625, 1628, 0, .none, s1625_zero_contract, 341, s1625_zero_checked⟩

def s1625_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1625_positive_checked : check 341 s1625_positive_contract = true := by decide +kernel
def s1625_positive : CertifiedContract :=
  ⟨1625, 1626, 1, (.dec 8), s1625_positive_contract, 341, s1625_positive_checked⟩

def s1626_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, true] 0 (.inc 7)⟩
theorem s1626_plain_checked : check 372 s1626_plain_contract = true := by decide +kernel
def s1626_plain : CertifiedContract :=
  ⟨1626, 1627, 0, (.inc 7), s1626_plain_contract, 372, s1626_plain_checked⟩

def s1627_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1627_plain_checked : check 91 s1627_plain_contract = true := by decide +kernel
def s1627_plain : CertifiedContract :=
  ⟨1627, 1625, 0, .none, s1627_plain_contract, 91, s1627_plain_checked⟩

def s1628_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1628_zero_checked : check 362 s1628_zero_contract = true := by decide +kernel
def s1628_zero : CertifiedContract :=
  ⟨1628, 1631, 0, .none, s1628_zero_contract, 362, s1628_zero_checked⟩

def s1628_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1628_positive_checked : check 368 s1628_positive_contract = true := by decide +kernel
def s1628_positive : CertifiedContract :=
  ⟨1628, 1629, 1, (.dec 2), s1628_positive_contract, 368, s1628_positive_checked⟩

def s1629_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1629_plain_checked : check 381 s1629_plain_contract = true := by decide +kernel
def s1629_plain : CertifiedContract :=
  ⟨1629, 1630, 0, (.inc 8), s1629_plain_contract, 381, s1629_plain_checked⟩

def s1630_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1630_plain_checked : check 100 s1630_plain_contract = true := by decide +kernel
def s1630_plain : CertifiedContract :=
  ⟨1630, 1628, 0, .none, s1630_plain_contract, 100, s1630_plain_checked⟩

def s1631_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1631_zero_checked : check 383 s1631_zero_contract = true := by decide +kernel
def s1631_zero : CertifiedContract :=
  ⟨1631, 1634, 0, .none, s1631_zero_contract, 383, s1631_zero_checked⟩

def s1631_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1631_positive_checked : check 389 s1631_positive_contract = true := by decide +kernel
def s1631_positive : CertifiedContract :=
  ⟨1631, 1632, 1, (.dec 0), s1631_positive_contract, 389, s1631_positive_checked⟩

def s1632_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1632_plain_checked : check 381 s1632_plain_contract = true := by decide +kernel
def s1632_plain : CertifiedContract :=
  ⟨1632, 1633, 0, (.inc 2), s1632_plain_contract, 381, s1632_plain_checked⟩

def s1633_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1633_plain_checked : check 103 s1633_plain_contract = true := by decide +kernel
def s1633_plain : CertifiedContract :=
  ⟨1633, 1631, 0, .none, s1633_plain_contract, 103, s1633_plain_checked⟩

def s1634_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1634_zero_checked : check 389 s1634_zero_contract = true := by decide +kernel
def s1634_zero : CertifiedContract :=
  ⟨1634, 1638, 0, .none, s1634_zero_contract, 389, s1634_zero_checked⟩

def s1634_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1634_positive_checked : check 395 s1634_positive_contract = true := by decide +kernel
def s1634_positive : CertifiedContract :=
  ⟨1634, 1635, 1, (.dec 2), s1634_positive_contract, 395, s1634_positive_checked⟩

def s1635_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1635_plain_checked : check 408 s1635_plain_contract = true := by decide +kernel
def s1635_plain : CertifiedContract :=
  ⟨1635, 1636, 0, (.inc 5), s1635_plain_contract, 408, s1635_plain_checked⟩

def s1636_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1636_plain_checked : check 435 s1636_plain_contract = true := by decide +kernel
def s1636_plain : CertifiedContract :=
  ⟨1636, 1637, 0, (.inc 8), s1636_plain_contract, 435, s1636_plain_checked⟩

def s1637_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1637_plain_checked : check 118 s1637_plain_contract = true := by decide +kernel
def s1637_plain : CertifiedContract :=
  ⟨1637, 1634, 0, .none, s1637_plain_contract, 118, s1637_plain_checked⟩

def s1638_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1638_zero_checked : check 410 s1638_zero_contract = true := by decide +kernel
def s1638_zero : CertifiedContract :=
  ⟨1638, 1644, 0, .none, s1638_zero_contract, 410, s1638_zero_checked⟩

def s1638_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1638_positive_checked : check 413 s1638_positive_contract = true := by decide +kernel
def s1638_positive : CertifiedContract :=
  ⟨1638, 1639, 1, (.dec 8), s1638_positive_contract, 413, s1638_positive_checked⟩

def s1639_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1639_plain_checked : check 408 s1639_plain_contract = true := by decide +kernel
def s1639_plain : CertifiedContract :=
  ⟨1639, 1640, 0, (.inc 5), s1639_plain_contract, 408, s1639_plain_checked⟩

def s1640_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1640_zero_checked : check 428 s1640_zero_contract = true := by decide +kernel
def s1640_zero : CertifiedContract :=
  ⟨1640, 1643, 0, .none, s1640_zero_contract, 428, s1640_zero_checked⟩

def s1640_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1640_positive_checked : check 431 s1640_positive_contract = true := by decide +kernel
def s1640_positive : CertifiedContract :=
  ⟨1640, 1641, 1, (.dec 8), s1640_positive_contract, 431, s1640_positive_checked⟩

def s1641_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1641_plain_checked : check 426 s1641_plain_contract = true := by decide +kernel
def s1641_plain : CertifiedContract :=
  ⟨1641, 1642, 0, (.inc 2), s1641_plain_contract, 426, s1641_plain_checked⟩

def s1642_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1642_plain_checked : check 118 s1642_plain_contract = true := by decide +kernel
def s1642_plain : CertifiedContract :=
  ⟨1642, 1640, 0, .none, s1642_plain_contract, 118, s1642_plain_checked⟩

def s1643_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1643_plain_checked : check 121 s1643_plain_contract = true := by decide +kernel
def s1643_plain : CertifiedContract :=
  ⟨1643, 1634, 0, .none, s1643_plain_contract, 121, s1643_plain_checked⟩

def s1644_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1644_zero_checked : check 398 s1644_zero_contract = true := by decide +kernel
def s1644_zero : CertifiedContract :=
  ⟨1644, 1647, 0, .none, s1644_zero_contract, 398, s1644_zero_checked⟩

def s1644_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1644_positive_checked : check 395 s1644_positive_contract = true := by decide +kernel
def s1644_positive : CertifiedContract :=
  ⟨1644, 1645, 1, (.dec 5), s1644_positive_contract, 395, s1644_positive_checked⟩

def s1645_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1645_plain_checked : check 408 s1645_plain_contract = true := by decide +kernel
def s1645_plain : CertifiedContract :=
  ⟨1645, 1646, 0, (.inc 0), s1645_plain_contract, 408, s1645_plain_checked⟩

def s1646_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1646_plain_checked : check 109 s1646_plain_contract = true := by decide +kernel
def s1646_plain : CertifiedContract :=
  ⟨1646, 1644, 0, .none, s1646_plain_contract, 109, s1646_plain_checked⟩

def s1647_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1647_zero_checked : check 362 s1647_zero_contract = true := by decide +kernel
def s1647_zero : CertifiedContract :=
  ⟨1647, 1651, 0, .none, s1647_zero_contract, 362, s1647_zero_checked⟩

def s1647_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s1647_positive_checked : check 368 s1647_positive_contract = true := by decide +kernel
def s1647_positive : CertifiedContract :=
  ⟨1647, 1648, 1, (.dec 3), s1647_positive_contract, 368, s1647_positive_checked⟩

def s1648_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1648_plain_checked : check 381 s1648_plain_contract = true := by decide +kernel
def s1648_plain : CertifiedContract :=
  ⟨1648, 1649, 0, (.inc 2), s1648_plain_contract, 381, s1648_plain_checked⟩

def s1649_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1649_plain_checked : check 408 s1649_plain_contract = true := by decide +kernel
def s1649_plain : CertifiedContract :=
  ⟨1649, 1650, 0, (.inc 8), s1649_plain_contract, 408, s1649_plain_checked⟩

def s1650_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1650_plain_checked : check 109 s1650_plain_contract = true := by decide +kernel
def s1650_plain : CertifiedContract :=
  ⟨1650, 1647, 0, .none, s1650_plain_contract, 109, s1650_plain_checked⟩

def s1651_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1651_zero_checked : check 368 s1651_zero_contract = true := by decide +kernel
def s1651_zero : CertifiedContract :=
  ⟨1651, 1654, 0, .none, s1651_zero_contract, 368, s1651_zero_checked⟩

def s1651_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1651_positive_checked : check 368 s1651_positive_contract = true := by decide +kernel
def s1651_positive : CertifiedContract :=
  ⟨1651, 1652, 1, (.dec 8), s1651_positive_contract, 368, s1651_positive_checked⟩

def s1652_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s1652_plain_checked : check 384 s1652_plain_contract = true := by decide +kernel
def s1652_plain : CertifiedContract :=
  ⟨1652, 1653, 0, (.inc 3), s1652_plain_contract, 384, s1652_plain_checked⟩

def s1653_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1653_plain_checked : check 100 s1653_plain_contract = true := by decide +kernel
def s1653_plain : CertifiedContract :=
  ⟨1653, 1651, 0, .none, s1653_plain_contract, 100, s1653_plain_checked⟩

def s1654_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1654_zero_checked : check 362 s1654_zero_contract = true := by decide +kernel
def s1654_zero : CertifiedContract :=
  ⟨1654, 1657, 0, .none, s1654_zero_contract, 362, s1654_zero_checked⟩

def s1654_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1654_positive_checked : check 368 s1654_positive_contract = true := by decide +kernel
def s1654_positive : CertifiedContract :=
  ⟨1654, 1655, 1, (.dec 2), s1654_positive_contract, 368, s1654_positive_checked⟩

def s1655_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1655_plain_checked : check 381 s1655_plain_contract = true := by decide +kernel
def s1655_plain : CertifiedContract :=
  ⟨1655, 1656, 0, (.inc 8), s1655_plain_contract, 381, s1655_plain_checked⟩

def s1656_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1656_plain_checked : check 100 s1656_plain_contract = true := by decide +kernel
def s1656_plain : CertifiedContract :=
  ⟨1656, 1654, 0, .none, s1656_plain_contract, 100, s1656_plain_checked⟩

def s1657_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1657_zero_checked : check 383 s1657_zero_contract = true := by decide +kernel
def s1657_zero : CertifiedContract :=
  ⟨1657, 1660, 0, .none, s1657_zero_contract, 383, s1657_zero_checked⟩

def s1657_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1657_positive_checked : check 389 s1657_positive_contract = true := by decide +kernel
def s1657_positive : CertifiedContract :=
  ⟨1657, 1658, 1, (.dec 0), s1657_positive_contract, 389, s1657_positive_checked⟩

def s1658_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1658_plain_checked : check 381 s1658_plain_contract = true := by decide +kernel
def s1658_plain : CertifiedContract :=
  ⟨1658, 1659, 0, (.inc 2), s1658_plain_contract, 381, s1658_plain_checked⟩

def s1659_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1659_plain_checked : check 103 s1659_plain_contract = true := by decide +kernel
def s1659_plain : CertifiedContract :=
  ⟨1659, 1657, 0, .none, s1659_plain_contract, 103, s1659_plain_checked⟩

def s1660_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1660_zero_checked : check 389 s1660_zero_contract = true := by decide +kernel
def s1660_zero : CertifiedContract :=
  ⟨1660, 1664, 0, .none, s1660_zero_contract, 389, s1660_zero_checked⟩

def s1660_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1660_positive_checked : check 395 s1660_positive_contract = true := by decide +kernel
def s1660_positive : CertifiedContract :=
  ⟨1660, 1661, 1, (.dec 2), s1660_positive_contract, 395, s1660_positive_checked⟩

def s1661_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1661_plain_checked : check 408 s1661_plain_contract = true := by decide +kernel
def s1661_plain : CertifiedContract :=
  ⟨1661, 1662, 0, (.inc 5), s1661_plain_contract, 408, s1661_plain_checked⟩

def s1662_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1662_plain_checked : check 435 s1662_plain_contract = true := by decide +kernel
def s1662_plain : CertifiedContract :=
  ⟨1662, 1663, 0, (.inc 8), s1662_plain_contract, 435, s1662_plain_checked⟩

def s1663_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1663_plain_checked : check 118 s1663_plain_contract = true := by decide +kernel
def s1663_plain : CertifiedContract :=
  ⟨1663, 1660, 0, .none, s1663_plain_contract, 118, s1663_plain_checked⟩

def s1664_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1664_zero_checked : check 410 s1664_zero_contract = true := by decide +kernel
def s1664_zero : CertifiedContract :=
  ⟨1664, 1670, 0, .none, s1664_zero_contract, 410, s1664_zero_checked⟩

def s1664_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1664_positive_checked : check 413 s1664_positive_contract = true := by decide +kernel
def s1664_positive : CertifiedContract :=
  ⟨1664, 1665, 1, (.dec 8), s1664_positive_contract, 413, s1664_positive_checked⟩

def s1665_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1665_plain_checked : check 408 s1665_plain_contract = true := by decide +kernel
def s1665_plain : CertifiedContract :=
  ⟨1665, 1666, 0, (.inc 5), s1665_plain_contract, 408, s1665_plain_checked⟩

def s1666_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1666_zero_checked : check 428 s1666_zero_contract = true := by decide +kernel
def s1666_zero : CertifiedContract :=
  ⟨1666, 1669, 0, .none, s1666_zero_contract, 428, s1666_zero_checked⟩

def s1666_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1666_positive_checked : check 431 s1666_positive_contract = true := by decide +kernel
def s1666_positive : CertifiedContract :=
  ⟨1666, 1667, 1, (.dec 8), s1666_positive_contract, 431, s1666_positive_checked⟩

def s1667_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1667_plain_checked : check 426 s1667_plain_contract = true := by decide +kernel
def s1667_plain : CertifiedContract :=
  ⟨1667, 1668, 0, (.inc 2), s1667_plain_contract, 426, s1667_plain_checked⟩

def s1668_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1668_plain_checked : check 118 s1668_plain_contract = true := by decide +kernel
def s1668_plain : CertifiedContract :=
  ⟨1668, 1666, 0, .none, s1668_plain_contract, 118, s1668_plain_checked⟩

def s1669_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1669_plain_checked : check 121 s1669_plain_contract = true := by decide +kernel
def s1669_plain : CertifiedContract :=
  ⟨1669, 1660, 0, .none, s1669_plain_contract, 121, s1669_plain_checked⟩

def s1670_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1670_zero_checked : check 398 s1670_zero_contract = true := by decide +kernel
def s1670_zero : CertifiedContract :=
  ⟨1670, 1673, 0, .none, s1670_zero_contract, 398, s1670_zero_checked⟩

def s1670_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1670_positive_checked : check 395 s1670_positive_contract = true := by decide +kernel
def s1670_positive : CertifiedContract :=
  ⟨1670, 1671, 1, (.dec 5), s1670_positive_contract, 395, s1670_positive_checked⟩

def s1671_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1671_plain_checked : check 408 s1671_plain_contract = true := by decide +kernel
def s1671_plain : CertifiedContract :=
  ⟨1671, 1672, 0, (.inc 0), s1671_plain_contract, 408, s1671_plain_checked⟩

def s1672_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1672_plain_checked : check 109 s1672_plain_contract = true := by decide +kernel
def s1672_plain : CertifiedContract :=
  ⟨1672, 1670, 0, .none, s1672_plain_contract, 109, s1672_plain_checked⟩

def s1673_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1673_zero_checked : check 362 s1673_zero_contract = true := by decide +kernel
def s1673_zero : CertifiedContract :=
  ⟨1673, 1677, 0, .none, s1673_zero_contract, 362, s1673_zero_checked⟩

def nonterminal : Array CertifiedContract := #[
  s1625_zero,
  s1625_positive,
  s1626_plain,
  s1627_plain,
  s1628_zero,
  s1628_positive,
  s1629_plain,
  s1630_plain,
  s1631_zero,
  s1631_positive,
  s1632_plain,
  s1633_plain,
  s1634_zero,
  s1634_positive,
  s1635_plain,
  s1636_plain,
  s1637_plain,
  s1638_zero,
  s1638_positive,
  s1639_plain,
  s1640_zero,
  s1640_positive,
  s1641_plain,
  s1642_plain,
  s1643_plain,
  s1644_zero,
  s1644_positive,
  s1645_plain,
  s1646_plain,
  s1647_zero,
  s1647_positive,
  s1648_plain,
  s1649_plain,
  s1650_plain,
  s1651_zero,
  s1651_positive,
  s1652_plain,
  s1653_plain,
  s1654_zero,
  s1654_positive,
  s1655_plain,
  s1656_plain,
  s1657_zero,
  s1657_positive,
  s1658_plain,
  s1659_plain,
  s1660_zero,
  s1660_positive,
  s1661_plain,
  s1662_plain,
  s1663_plain,
  s1664_zero,
  s1664_positive,
  s1665_plain,
  s1666_zero,
  s1666_positive,
  s1667_plain,
  s1668_plain,
  s1669_plain,
  s1670_zero,
  s1670_positive,
  s1671_plain,
  s1672_plain,
  s1673_zero
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S033
