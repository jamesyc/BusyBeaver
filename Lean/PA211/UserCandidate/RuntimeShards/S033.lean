import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S033
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1625_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1625_zero_checked : check 342 s1625_zero_contract = true := by decide +kernel
def s1625_zero : CertifiedContract :=
  ⟨1625, 1628, 0, .none, s1625_zero_contract, 342, s1625_zero_checked⟩

def s1625_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1625_positive_checked : check 342 s1625_positive_contract = true := by decide +kernel
def s1625_positive : CertifiedContract :=
  ⟨1625, 1626, 1, (.dec 8), s1625_positive_contract, 342, s1625_positive_checked⟩

def s1626_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, true] 0 (.inc 7)⟩
theorem s1626_plain_checked : check 373 s1626_plain_contract = true := by decide +kernel
def s1626_plain : CertifiedContract :=
  ⟨1626, 1627, 0, (.inc 7), s1626_plain_contract, 373, s1626_plain_checked⟩

def s1627_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1627_plain_checked : check 92 s1627_plain_contract = true := by decide +kernel
def s1627_plain : CertifiedContract :=
  ⟨1627, 1625, 0, .none, s1627_plain_contract, 92, s1627_plain_checked⟩

def s1628_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1628_zero_checked : check 363 s1628_zero_contract = true := by decide +kernel
def s1628_zero : CertifiedContract :=
  ⟨1628, 1631, 0, .none, s1628_zero_contract, 363, s1628_zero_checked⟩

def s1628_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1628_positive_checked : check 369 s1628_positive_contract = true := by decide +kernel
def s1628_positive : CertifiedContract :=
  ⟨1628, 1629, 1, (.dec 2), s1628_positive_contract, 369, s1628_positive_checked⟩

def s1629_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1629_plain_checked : check 382 s1629_plain_contract = true := by decide +kernel
def s1629_plain : CertifiedContract :=
  ⟨1629, 1630, 0, (.inc 8), s1629_plain_contract, 382, s1629_plain_checked⟩

def s1630_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1630_plain_checked : check 101 s1630_plain_contract = true := by decide +kernel
def s1630_plain : CertifiedContract :=
  ⟨1630, 1628, 0, .none, s1630_plain_contract, 101, s1630_plain_checked⟩

def s1631_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1631_zero_checked : check 384 s1631_zero_contract = true := by decide +kernel
def s1631_zero : CertifiedContract :=
  ⟨1631, 1634, 0, .none, s1631_zero_contract, 384, s1631_zero_checked⟩

def s1631_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1631_positive_checked : check 390 s1631_positive_contract = true := by decide +kernel
def s1631_positive : CertifiedContract :=
  ⟨1631, 1632, 1, (.dec 0), s1631_positive_contract, 390, s1631_positive_checked⟩

def s1632_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1632_plain_checked : check 382 s1632_plain_contract = true := by decide +kernel
def s1632_plain : CertifiedContract :=
  ⟨1632, 1633, 0, (.inc 2), s1632_plain_contract, 382, s1632_plain_checked⟩

def s1633_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1633_plain_checked : check 104 s1633_plain_contract = true := by decide +kernel
def s1633_plain : CertifiedContract :=
  ⟨1633, 1631, 0, .none, s1633_plain_contract, 104, s1633_plain_checked⟩

def s1634_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1634_zero_checked : check 390 s1634_zero_contract = true := by decide +kernel
def s1634_zero : CertifiedContract :=
  ⟨1634, 1638, 0, .none, s1634_zero_contract, 390, s1634_zero_checked⟩

def s1634_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1634_positive_checked : check 396 s1634_positive_contract = true := by decide +kernel
def s1634_positive : CertifiedContract :=
  ⟨1634, 1635, 1, (.dec 2), s1634_positive_contract, 396, s1634_positive_checked⟩

def s1635_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1635_plain_checked : check 409 s1635_plain_contract = true := by decide +kernel
def s1635_plain : CertifiedContract :=
  ⟨1635, 1636, 0, (.inc 5), s1635_plain_contract, 409, s1635_plain_checked⟩

def s1636_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1636_plain_checked : check 436 s1636_plain_contract = true := by decide +kernel
def s1636_plain : CertifiedContract :=
  ⟨1636, 1637, 0, (.inc 8), s1636_plain_contract, 436, s1636_plain_checked⟩

def s1637_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1637_plain_checked : check 119 s1637_plain_contract = true := by decide +kernel
def s1637_plain : CertifiedContract :=
  ⟨1637, 1634, 0, .none, s1637_plain_contract, 119, s1637_plain_checked⟩

def s1638_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1638_zero_checked : check 411 s1638_zero_contract = true := by decide +kernel
def s1638_zero : CertifiedContract :=
  ⟨1638, 1644, 0, .none, s1638_zero_contract, 411, s1638_zero_checked⟩

def s1638_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1638_positive_checked : check 414 s1638_positive_contract = true := by decide +kernel
def s1638_positive : CertifiedContract :=
  ⟨1638, 1639, 1, (.dec 8), s1638_positive_contract, 414, s1638_positive_checked⟩

def s1639_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1639_plain_checked : check 409 s1639_plain_contract = true := by decide +kernel
def s1639_plain : CertifiedContract :=
  ⟨1639, 1640, 0, (.inc 5), s1639_plain_contract, 409, s1639_plain_checked⟩

def s1640_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1640_zero_checked : check 429 s1640_zero_contract = true := by decide +kernel
def s1640_zero : CertifiedContract :=
  ⟨1640, 1643, 0, .none, s1640_zero_contract, 429, s1640_zero_checked⟩

def s1640_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1640_positive_checked : check 432 s1640_positive_contract = true := by decide +kernel
def s1640_positive : CertifiedContract :=
  ⟨1640, 1641, 1, (.dec 8), s1640_positive_contract, 432, s1640_positive_checked⟩

def s1641_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1641_plain_checked : check 427 s1641_plain_contract = true := by decide +kernel
def s1641_plain : CertifiedContract :=
  ⟨1641, 1642, 0, (.inc 2), s1641_plain_contract, 427, s1641_plain_checked⟩

def s1642_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1642_plain_checked : check 119 s1642_plain_contract = true := by decide +kernel
def s1642_plain : CertifiedContract :=
  ⟨1642, 1640, 0, .none, s1642_plain_contract, 119, s1642_plain_checked⟩

def s1643_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1643_plain_checked : check 122 s1643_plain_contract = true := by decide +kernel
def s1643_plain : CertifiedContract :=
  ⟨1643, 1634, 0, .none, s1643_plain_contract, 122, s1643_plain_checked⟩

def s1644_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1644_zero_checked : check 399 s1644_zero_contract = true := by decide +kernel
def s1644_zero : CertifiedContract :=
  ⟨1644, 1647, 0, .none, s1644_zero_contract, 399, s1644_zero_checked⟩

def s1644_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1644_positive_checked : check 396 s1644_positive_contract = true := by decide +kernel
def s1644_positive : CertifiedContract :=
  ⟨1644, 1645, 1, (.dec 5), s1644_positive_contract, 396, s1644_positive_checked⟩

def s1645_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1645_plain_checked : check 409 s1645_plain_contract = true := by decide +kernel
def s1645_plain : CertifiedContract :=
  ⟨1645, 1646, 0, (.inc 0), s1645_plain_contract, 409, s1645_plain_checked⟩

def s1646_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1646_plain_checked : check 110 s1646_plain_contract = true := by decide +kernel
def s1646_plain : CertifiedContract :=
  ⟨1646, 1644, 0, .none, s1646_plain_contract, 110, s1646_plain_checked⟩

def s1647_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1647_zero_checked : check 363 s1647_zero_contract = true := by decide +kernel
def s1647_zero : CertifiedContract :=
  ⟨1647, 1651, 0, .none, s1647_zero_contract, 363, s1647_zero_checked⟩

def s1647_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s1647_positive_checked : check 369 s1647_positive_contract = true := by decide +kernel
def s1647_positive : CertifiedContract :=
  ⟨1647, 1648, 1, (.dec 3), s1647_positive_contract, 369, s1647_positive_checked⟩

def s1648_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1648_plain_checked : check 382 s1648_plain_contract = true := by decide +kernel
def s1648_plain : CertifiedContract :=
  ⟨1648, 1649, 0, (.inc 2), s1648_plain_contract, 382, s1648_plain_checked⟩

def s1649_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1649_plain_checked : check 409 s1649_plain_contract = true := by decide +kernel
def s1649_plain : CertifiedContract :=
  ⟨1649, 1650, 0, (.inc 8), s1649_plain_contract, 409, s1649_plain_checked⟩

def s1650_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1650_plain_checked : check 110 s1650_plain_contract = true := by decide +kernel
def s1650_plain : CertifiedContract :=
  ⟨1650, 1647, 0, .none, s1650_plain_contract, 110, s1650_plain_checked⟩

def s1651_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1651_zero_checked : check 369 s1651_zero_contract = true := by decide +kernel
def s1651_zero : CertifiedContract :=
  ⟨1651, 1654, 0, .none, s1651_zero_contract, 369, s1651_zero_checked⟩

def s1651_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1651_positive_checked : check 369 s1651_positive_contract = true := by decide +kernel
def s1651_positive : CertifiedContract :=
  ⟨1651, 1652, 1, (.dec 8), s1651_positive_contract, 369, s1651_positive_checked⟩

def s1652_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s1652_plain_checked : check 385 s1652_plain_contract = true := by decide +kernel
def s1652_plain : CertifiedContract :=
  ⟨1652, 1653, 0, (.inc 3), s1652_plain_contract, 385, s1652_plain_checked⟩

def s1653_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1653_plain_checked : check 101 s1653_plain_contract = true := by decide +kernel
def s1653_plain : CertifiedContract :=
  ⟨1653, 1651, 0, .none, s1653_plain_contract, 101, s1653_plain_checked⟩

def s1654_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1654_zero_checked : check 363 s1654_zero_contract = true := by decide +kernel
def s1654_zero : CertifiedContract :=
  ⟨1654, 1657, 0, .none, s1654_zero_contract, 363, s1654_zero_checked⟩

def s1654_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1654_positive_checked : check 369 s1654_positive_contract = true := by decide +kernel
def s1654_positive : CertifiedContract :=
  ⟨1654, 1655, 1, (.dec 2), s1654_positive_contract, 369, s1654_positive_checked⟩

def s1655_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1655_plain_checked : check 382 s1655_plain_contract = true := by decide +kernel
def s1655_plain : CertifiedContract :=
  ⟨1655, 1656, 0, (.inc 8), s1655_plain_contract, 382, s1655_plain_checked⟩

def s1656_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1656_plain_checked : check 101 s1656_plain_contract = true := by decide +kernel
def s1656_plain : CertifiedContract :=
  ⟨1656, 1654, 0, .none, s1656_plain_contract, 101, s1656_plain_checked⟩

def s1657_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1657_zero_checked : check 384 s1657_zero_contract = true := by decide +kernel
def s1657_zero : CertifiedContract :=
  ⟨1657, 1660, 0, .none, s1657_zero_contract, 384, s1657_zero_checked⟩

def s1657_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1657_positive_checked : check 390 s1657_positive_contract = true := by decide +kernel
def s1657_positive : CertifiedContract :=
  ⟨1657, 1658, 1, (.dec 0), s1657_positive_contract, 390, s1657_positive_checked⟩

def s1658_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1658_plain_checked : check 382 s1658_plain_contract = true := by decide +kernel
def s1658_plain : CertifiedContract :=
  ⟨1658, 1659, 0, (.inc 2), s1658_plain_contract, 382, s1658_plain_checked⟩

def s1659_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1659_plain_checked : check 104 s1659_plain_contract = true := by decide +kernel
def s1659_plain : CertifiedContract :=
  ⟨1659, 1657, 0, .none, s1659_plain_contract, 104, s1659_plain_checked⟩

def s1660_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1660_zero_checked : check 390 s1660_zero_contract = true := by decide +kernel
def s1660_zero : CertifiedContract :=
  ⟨1660, 1664, 0, .none, s1660_zero_contract, 390, s1660_zero_checked⟩

def s1660_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1660_positive_checked : check 396 s1660_positive_contract = true := by decide +kernel
def s1660_positive : CertifiedContract :=
  ⟨1660, 1661, 1, (.dec 2), s1660_positive_contract, 396, s1660_positive_checked⟩

def s1661_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1661_plain_checked : check 409 s1661_plain_contract = true := by decide +kernel
def s1661_plain : CertifiedContract :=
  ⟨1661, 1662, 0, (.inc 5), s1661_plain_contract, 409, s1661_plain_checked⟩

def s1662_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1662_plain_checked : check 436 s1662_plain_contract = true := by decide +kernel
def s1662_plain : CertifiedContract :=
  ⟨1662, 1663, 0, (.inc 8), s1662_plain_contract, 436, s1662_plain_checked⟩

def s1663_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1663_plain_checked : check 119 s1663_plain_contract = true := by decide +kernel
def s1663_plain : CertifiedContract :=
  ⟨1663, 1660, 0, .none, s1663_plain_contract, 119, s1663_plain_checked⟩

def s1664_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1664_zero_checked : check 411 s1664_zero_contract = true := by decide +kernel
def s1664_zero : CertifiedContract :=
  ⟨1664, 1670, 0, .none, s1664_zero_contract, 411, s1664_zero_checked⟩

def s1664_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1664_positive_checked : check 414 s1664_positive_contract = true := by decide +kernel
def s1664_positive : CertifiedContract :=
  ⟨1664, 1665, 1, (.dec 8), s1664_positive_contract, 414, s1664_positive_checked⟩

def s1665_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1665_plain_checked : check 409 s1665_plain_contract = true := by decide +kernel
def s1665_plain : CertifiedContract :=
  ⟨1665, 1666, 0, (.inc 5), s1665_plain_contract, 409, s1665_plain_checked⟩

def s1666_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1666_zero_checked : check 429 s1666_zero_contract = true := by decide +kernel
def s1666_zero : CertifiedContract :=
  ⟨1666, 1669, 0, .none, s1666_zero_contract, 429, s1666_zero_checked⟩

def s1666_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1666_positive_checked : check 432 s1666_positive_contract = true := by decide +kernel
def s1666_positive : CertifiedContract :=
  ⟨1666, 1667, 1, (.dec 8), s1666_positive_contract, 432, s1666_positive_checked⟩

def s1667_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1667_plain_checked : check 427 s1667_plain_contract = true := by decide +kernel
def s1667_plain : CertifiedContract :=
  ⟨1667, 1668, 0, (.inc 2), s1667_plain_contract, 427, s1667_plain_checked⟩

def s1668_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1668_plain_checked : check 119 s1668_plain_contract = true := by decide +kernel
def s1668_plain : CertifiedContract :=
  ⟨1668, 1666, 0, .none, s1668_plain_contract, 119, s1668_plain_checked⟩

def s1669_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1669_plain_checked : check 122 s1669_plain_contract = true := by decide +kernel
def s1669_plain : CertifiedContract :=
  ⟨1669, 1660, 0, .none, s1669_plain_contract, 122, s1669_plain_checked⟩

def s1670_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1670_zero_checked : check 399 s1670_zero_contract = true := by decide +kernel
def s1670_zero : CertifiedContract :=
  ⟨1670, 1673, 0, .none, s1670_zero_contract, 399, s1670_zero_checked⟩

def s1670_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1670_positive_checked : check 396 s1670_positive_contract = true := by decide +kernel
def s1670_positive : CertifiedContract :=
  ⟨1670, 1671, 1, (.dec 5), s1670_positive_contract, 396, s1670_positive_checked⟩

def s1671_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1671_plain_checked : check 409 s1671_plain_contract = true := by decide +kernel
def s1671_plain : CertifiedContract :=
  ⟨1671, 1672, 0, (.inc 0), s1671_plain_contract, 409, s1671_plain_checked⟩

def s1672_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1672_plain_checked : check 110 s1672_plain_contract = true := by decide +kernel
def s1672_plain : CertifiedContract :=
  ⟨1672, 1670, 0, .none, s1672_plain_contract, 110, s1672_plain_checked⟩

def s1673_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1673_zero_checked : check 363 s1673_zero_contract = true := by decide +kernel
def s1673_zero : CertifiedContract :=
  ⟨1673, 1677, 0, .none, s1673_zero_contract, 363, s1673_zero_checked⟩

end PA211.UserCandidate.RuntimeShards.S033
