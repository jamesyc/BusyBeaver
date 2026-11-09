import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S034
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1673_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, true, false] 1 (.dec 4)⟩
theorem s1673_positive_checked : check 369 s1673_positive_contract = true := by decide +kernel
def s1673_positive : CertifiedContract :=
  ⟨1673, 1674, 1, (.dec 4), s1673_positive_contract, 369, s1673_positive_checked⟩

def s1674_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1674_plain_checked : check 382 s1674_plain_contract = true := by decide +kernel
def s1674_plain : CertifiedContract :=
  ⟨1674, 1675, 0, (.inc 2), s1674_plain_contract, 382, s1674_plain_checked⟩

def s1675_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1675_plain_checked : check 409 s1675_plain_contract = true := by decide +kernel
def s1675_plain : CertifiedContract :=
  ⟨1675, 1676, 0, (.inc 8), s1675_plain_contract, 409, s1675_plain_checked⟩

def s1676_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1676_plain_checked : check 110 s1676_plain_contract = true := by decide +kernel
def s1676_plain : CertifiedContract :=
  ⟨1676, 1673, 0, .none, s1676_plain_contract, 110, s1676_plain_checked⟩

def s1677_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1677_zero_checked : check 372 s1677_zero_contract = true := by decide +kernel
def s1677_zero : CertifiedContract :=
  ⟨1677, 1680, 0, .none, s1677_zero_contract, 372, s1677_zero_checked⟩

def s1677_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1677_positive_checked : check 369 s1677_positive_contract = true := by decide +kernel
def s1677_positive : CertifiedContract :=
  ⟨1677, 1678, 1, (.dec 8), s1677_positive_contract, 369, s1677_positive_checked⟩

def s1678_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, true, true, true] 0 (.inc 4)⟩
theorem s1678_plain_checked : check 373 s1678_plain_contract = true := by decide +kernel
def s1678_plain : CertifiedContract :=
  ⟨1678, 1679, 0, (.inc 4), s1678_plain_contract, 373, s1678_plain_checked⟩

def s1679_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1679_plain_checked : check 101 s1679_plain_contract = true := by decide +kernel
def s1679_plain : CertifiedContract :=
  ⟨1679, 1677, 0, .none, s1679_plain_contract, 101, s1679_plain_checked⟩

def s1680_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1680_zero_checked : check 375 s1680_zero_contract = true := by decide +kernel
def s1680_zero : CertifiedContract :=
  ⟨1680, 1688, 0, .none, s1680_zero_contract, 375, s1680_zero_checked⟩

def s1680_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1680_positive_checked : check 381 s1680_positive_contract = true := by decide +kernel
def s1680_positive : CertifiedContract :=
  ⟨1680, 1681, 1, (.dec 0), s1680_positive_contract, 381, s1680_positive_checked⟩

def s1681_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1681_plain_checked : check 391 s1681_plain_contract = true := by decide +kernel
def s1681_plain : CertifiedContract :=
  ⟨1681, 1682, 0, (.inc 5), s1681_plain_contract, 391, s1681_plain_checked⟩

def s1682_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1682_zero_checked : check 417 s1682_zero_contract = true := by decide +kernel
def s1682_zero : CertifiedContract :=
  ⟨1682, 1684, 0, .none, s1682_zero_contract, 417, s1682_zero_checked⟩

def s1682_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1682_positive_checked : check 423 s1682_positive_contract = true := by decide +kernel
def s1682_positive : CertifiedContract :=
  ⟨1682, 1683, 1, (.dec 8), s1682_positive_contract, 423, s1682_positive_checked⟩

def s1683_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1683_plain_checked : check 116 s1683_plain_contract = true := by decide +kernel
def s1683_plain : CertifiedContract :=
  ⟨1683, 1687, 0, .none, s1683_plain_contract, 116, s1683_plain_checked⟩

def s1684_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1684_zero_checked : check 429 s1684_zero_contract = true := by decide +kernel
def s1684_zero : CertifiedContract :=
  ⟨1684, 1687, 0, .none, s1684_zero_contract, 429, s1684_zero_checked⟩

def s1684_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1684_positive_checked : check 432 s1684_positive_contract = true := by decide +kernel
def s1684_positive : CertifiedContract :=
  ⟨1684, 1685, 1, (.dec 5), s1684_positive_contract, 432, s1684_positive_checked⟩

def s1685_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1685_plain_checked : check 436 s1685_plain_contract = true := by decide +kernel
def s1685_plain : CertifiedContract :=
  ⟨1685, 1686, 0, (.inc 8), s1685_plain_contract, 436, s1685_plain_checked⟩

def s1686_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1686_plain_checked : check 119 s1686_plain_contract = true := by decide +kernel
def s1686_plain : CertifiedContract :=
  ⟨1686, 1684, 0, .none, s1686_plain_contract, 119, s1686_plain_checked⟩

def s1687_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1687_plain_checked : check 110 s1687_plain_contract = true := by decide +kernel
def s1687_plain : CertifiedContract :=
  ⟨1687, 1680, 0, .none, s1687_plain_contract, 110, s1687_plain_checked⟩

def s1688_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1688_zero_checked : check 375 s1688_zero_contract = true := by decide +kernel
def s1688_zero : CertifiedContract :=
  ⟨1688, 1691, 0, .none, s1688_zero_contract, 375, s1688_zero_checked⟩

def s1688_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1688_positive_checked : check 378 s1688_positive_contract = true := by decide +kernel
def s1688_positive : CertifiedContract :=
  ⟨1688, 1689, 1, (.dec 5), s1688_positive_contract, 378, s1688_positive_checked⟩

def s1689_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1689_plain_checked : check 391 s1689_plain_contract = true := by decide +kernel
def s1689_plain : CertifiedContract :=
  ⟨1689, 1690, 0, (.inc 0), s1689_plain_contract, 391, s1689_plain_checked⟩

def s1690_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1690_plain_checked : check 104 s1690_plain_contract = true := by decide +kernel
def s1690_plain : CertifiedContract :=
  ⟨1690, 1688, 0, .none, s1690_plain_contract, 104, s1690_plain_checked⟩

def s1691_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s1691_zero_checked : check 372 s1691_zero_contract = true := by decide +kernel
def s1691_zero : CertifiedContract :=
  ⟨1691, 1695, 0, .none, s1691_zero_contract, 372, s1691_zero_checked⟩

def s1691_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1691_positive_checked : check 378 s1691_positive_contract = true := by decide +kernel
def s1691_positive : CertifiedContract :=
  ⟨1691, 1692, 1, (.dec 2), s1691_positive_contract, 378, s1691_positive_checked⟩

def s1692_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1692_plain_checked : check 391 s1692_plain_contract = true := by decide +kernel
def s1692_plain : CertifiedContract :=
  ⟨1692, 1693, 0, (.inc 5), s1692_plain_contract, 391, s1692_plain_checked⟩

def s1693_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1693_plain_checked : check 418 s1693_plain_contract = true := by decide +kernel
def s1693_plain : CertifiedContract :=
  ⟨1693, 1694, 0, (.inc 8), s1693_plain_contract, 418, s1693_plain_checked⟩

def s1694_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1694_plain_checked : check 113 s1694_plain_contract = true := by decide +kernel
def s1694_plain : CertifiedContract :=
  ⟨1694, 1691, 0, .none, s1694_plain_contract, 113, s1694_plain_checked⟩

def s1695_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1695_zero_checked : check 393 s1695_zero_contract = true := by decide +kernel
def s1695_zero : CertifiedContract :=
  ⟨1695, 1701, 0, .none, s1695_zero_contract, 393, s1695_zero_checked⟩

def s1695_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1695_positive_checked : check 396 s1695_positive_contract = true := by decide +kernel
def s1695_positive : CertifiedContract :=
  ⟨1695, 1696, 1, (.dec 8), s1695_positive_contract, 396, s1695_positive_checked⟩

def s1696_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1696_plain_checked : check 391 s1696_plain_contract = true := by decide +kernel
def s1696_plain : CertifiedContract :=
  ⟨1696, 1697, 0, (.inc 5), s1696_plain_contract, 391, s1696_plain_checked⟩

def s1697_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s1697_zero_checked : check 411 s1697_zero_contract = true := by decide +kernel
def s1697_zero : CertifiedContract :=
  ⟨1697, 1700, 0, .none, s1697_zero_contract, 411, s1697_zero_checked⟩

def s1697_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1697_positive_checked : check 414 s1697_positive_contract = true := by decide +kernel
def s1697_positive : CertifiedContract :=
  ⟨1697, 1698, 1, (.dec 8), s1697_positive_contract, 414, s1697_positive_checked⟩

def s1698_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1698_plain_checked : check 409 s1698_plain_contract = true := by decide +kernel
def s1698_plain : CertifiedContract :=
  ⟨1698, 1699, 0, (.inc 2), s1698_plain_contract, 409, s1698_plain_checked⟩

def s1699_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1699_plain_checked : check 113 s1699_plain_contract = true := by decide +kernel
def s1699_plain : CertifiedContract :=
  ⟨1699, 1697, 0, .none, s1699_plain_contract, 113, s1699_plain_checked⟩

def s1700_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1700_plain_checked : check 116 s1700_plain_contract = true := by decide +kernel
def s1700_plain : CertifiedContract :=
  ⟨1700, 1691, 0, .none, s1700_plain_contract, 116, s1700_plain_checked⟩

def s1701_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, true, false] 0 .none⟩
theorem s1701_zero_checked : check 378 s1701_zero_contract = true := by decide +kernel
def s1701_zero : CertifiedContract :=
  ⟨1701, 1707, 0, .none, s1701_zero_contract, 378, s1701_zero_checked⟩

def s1701_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1701_positive_checked : check 378 s1701_positive_contract = true := by decide +kernel
def s1701_positive : CertifiedContract :=
  ⟨1701, 1702, 1, (.dec 5), s1701_positive_contract, 378, s1701_positive_checked⟩

def s1702_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1702_plain_checked : check 391 s1702_plain_contract = true := by decide +kernel
def s1702_plain : CertifiedContract :=
  ⟨1702, 1703, 0, (.inc 2), s1702_plain_contract, 391, s1702_plain_checked⟩

def s1703_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1703_plain_checked : check 394 s1703_plain_contract = true := by decide +kernel
def s1703_plain : CertifiedContract :=
  ⟨1703, 1704, 0, (.inc 2), s1703_plain_contract, 394, s1703_plain_checked⟩

def s1704_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1704_plain_checked : check 400 s1704_plain_contract = true := by decide +kernel
def s1704_plain : CertifiedContract :=
  ⟨1704, 1705, 0, (.inc 2), s1704_plain_contract, 400, s1704_plain_checked⟩

def s1705_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1705_plain_checked : check 406 s1705_plain_contract = true := by decide +kernel
def s1705_plain : CertifiedContract :=
  ⟨1705, 1706, 0, (.inc 2), s1705_plain_contract, 406, s1705_plain_checked⟩

def s1706_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1706_plain_checked : check 101 s1706_plain_contract = true := by decide +kernel
def s1706_plain : CertifiedContract :=
  ⟨1706, 1701, 0, .none, s1706_plain_contract, 101, s1706_plain_checked⟩

def s1707_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1707_plain_checked : check 346 s1707_plain_contract = true := by decide +kernel
def s1707_plain : CertifiedContract :=
  ⟨1707, 1708, 0, (.inc 2), s1707_plain_contract, 346, s1707_plain_checked⟩

def s1708_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s1708_plain_checked : check 355 s1708_plain_contract = true := by decide +kernel
def s1708_plain : CertifiedContract :=
  ⟨1708, 1709, 0, (.inc 2), s1708_plain_contract, 355, s1708_plain_checked⟩

def s1709_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s1709_zero_checked : check 384 s1709_zero_contract = true := by decide +kernel
def s1709_zero : CertifiedContract :=
  ⟨1709, 1717, 0, .none, s1709_zero_contract, 384, s1709_zero_checked⟩

def s1709_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1709_positive_checked : check 390 s1709_positive_contract = true := by decide +kernel
def s1709_positive : CertifiedContract :=
  ⟨1709, 1710, 1, (.dec 0), s1709_positive_contract, 390, s1709_positive_checked⟩

def s1710_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1710_plain_checked : check 400 s1710_plain_contract = true := by decide +kernel
def s1710_plain : CertifiedContract :=
  ⟨1710, 1711, 0, (.inc 5), s1710_plain_contract, 400, s1710_plain_checked⟩

def s1711_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1711_zero_checked : check 426 s1711_zero_contract = true := by decide +kernel
def s1711_zero : CertifiedContract :=
  ⟨1711, 1713, 0, .none, s1711_zero_contract, 426, s1711_zero_checked⟩

def s1711_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1711_positive_checked : check 432 s1711_positive_contract = true := by decide +kernel
def s1711_positive : CertifiedContract :=
  ⟨1711, 1712, 1, (.dec 8), s1711_positive_contract, 432, s1711_positive_checked⟩

def s1712_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s1712_plain_checked : check 119 s1712_plain_contract = true := by decide +kernel
def s1712_plain : CertifiedContract :=
  ⟨1712, 1716, 0, .none, s1712_plain_contract, 119, s1712_plain_checked⟩

def s1713_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s1713_zero_checked : check 438 s1713_zero_contract = true := by decide +kernel
def s1713_zero : CertifiedContract :=
  ⟨1713, 1716, 0, .none, s1713_zero_contract, 438, s1713_zero_checked⟩

def s1713_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1713_positive_checked : check 441 s1713_positive_contract = true := by decide +kernel
def s1713_positive : CertifiedContract :=
  ⟨1713, 1714, 1, (.dec 5), s1713_positive_contract, 441, s1713_positive_checked⟩

def s1714_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1714_plain_checked : check 445 s1714_plain_contract = true := by decide +kernel
def s1714_plain : CertifiedContract :=
  ⟨1714, 1715, 0, (.inc 8), s1714_plain_contract, 445, s1714_plain_checked⟩

def s1715_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1715_plain_checked : check 122 s1715_plain_contract = true := by decide +kernel
def s1715_plain : CertifiedContract :=
  ⟨1715, 1713, 0, .none, s1715_plain_contract, 122, s1715_plain_checked⟩

def s1716_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s1716_plain_checked : check 113 s1716_plain_contract = true := by decide +kernel
def s1716_plain : CertifiedContract :=
  ⟨1716, 1709, 0, .none, s1716_plain_contract, 113, s1716_plain_checked⟩

def s1717_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s1717_zero_checked : check 384 s1717_zero_contract = true := by decide +kernel
def s1717_zero : CertifiedContract :=
  ⟨1717, 1720, 0, .none, s1717_zero_contract, 384, s1717_zero_checked⟩

def s1717_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1717_positive_checked : check 387 s1717_positive_contract = true := by decide +kernel
def s1717_positive : CertifiedContract :=
  ⟨1717, 1718, 1, (.dec 5), s1717_positive_contract, 387, s1717_positive_checked⟩

def s1718_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1718_plain_checked : check 400 s1718_plain_contract = true := by decide +kernel
def s1718_plain : CertifiedContract :=
  ⟨1718, 1719, 0, (.inc 0), s1718_plain_contract, 400, s1718_plain_checked⟩

def s1719_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s1719_plain_checked : check 107 s1719_plain_contract = true := by decide +kernel
def s1719_plain : CertifiedContract :=
  ⟨1719, 1717, 0, .none, s1719_plain_contract, 107, s1719_plain_checked⟩

def s1720_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, false] 0 .none⟩
theorem s1720_zero_checked : check 381 s1720_zero_contract = true := by decide +kernel
def s1720_zero : CertifiedContract :=
  ⟨1720, 1724, 0, .none, s1720_zero_contract, 381, s1720_zero_checked⟩

def s1720_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1720_positive_checked : check 387 s1720_positive_contract = true := by decide +kernel
def s1720_positive : CertifiedContract :=
  ⟨1720, 1721, 1, (.dec 2), s1720_positive_contract, 387, s1720_positive_checked⟩

def s1721_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1721_plain_checked : check 400 s1721_plain_contract = true := by decide +kernel
def s1721_plain : CertifiedContract :=
  ⟨1721, 1722, 0, (.inc 5), s1721_plain_contract, 400, s1721_plain_checked⟩

def s1722_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1722_plain_checked : check 427 s1722_plain_contract = true := by decide +kernel
def s1722_plain : CertifiedContract :=
  ⟨1722, 1723, 0, (.inc 8), s1722_plain_contract, 427, s1722_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S034
