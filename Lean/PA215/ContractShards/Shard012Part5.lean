import PA215.CertifiedContracts
import PA215.Census.C012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard012Part5
open PA215.Contracts PA215.Census

def original1622 : RawOriginal := C012.records[86]'(by decide)
theorem original_id1622 : original1622.index = 1622 := by decide

def c1622 : Contract := original1622.toContract.get (by decide)
theorem binding1622 : original1622.toContract = some c1622 := rfl

theorem checked1622 : check 4000 c1622 = true := by decide

def original1623 : RawOriginal := C012.records[87]'(by decide)
theorem original_id1623 : original1623.index = 1623 := by decide

def c1623 : Contract := original1623.toContract.get (by decide)
theorem binding1623 : original1623.toContract = some c1623 := rfl

theorem checked1623 : check 4000 c1623 = true := by decide

def original1624 : RawOriginal := C012.records[88]'(by decide)
theorem original_id1624 : original1624.index = 1624 := by decide

def c1624 : Contract := original1624.toContract.get (by decide)
theorem binding1624 : original1624.toContract = some c1624 := rfl

theorem checked1624 : check 4000 c1624 = true := by decide

def original1625 : RawOriginal := C012.records[89]'(by decide)
theorem original_id1625 : original1625.index = 1625 := by decide

def c1625 : Contract := original1625.toContract.get (by decide)
theorem binding1625 : original1625.toContract = some c1625 := rfl

theorem checked1625 : check 4000 c1625 = true := by decide

def original1626 : RawOriginal := C012.records[90]'(by decide)
theorem original_id1626 : original1626.index = 1626 := by decide

def c1626 : Contract := original1626.toContract.get (by decide)
theorem binding1626 : original1626.toContract = some c1626 := rfl

theorem checked1626 : check 4000 c1626 = true := by decide

def original1627 : RawOriginal := C012.records[91]'(by decide)
theorem original_id1627 : original1627.index = 1627 := by decide

def c1627 : Contract := original1627.toContract.get (by decide)
theorem binding1627 : original1627.toContract = some c1627 := rfl

theorem checked1627 : check 4000 c1627 = true := by decide

def original1628 : RawOriginal := C012.records[92]'(by decide)
theorem original_id1628 : original1628.index = 1628 := by decide

def c1628 : Contract := original1628.toContract.get (by decide)
theorem binding1628 : original1628.toContract = some c1628 := rfl

theorem checked1628 : check 4000 c1628 = true := by decide

def original1629 : RawOriginal := C012.records[93]'(by decide)
theorem original_id1629 : original1629.index = 1629 := by decide

def c1629 : Contract := original1629.toContract.get (by decide)
theorem binding1629 : original1629.toContract = some c1629 := rfl

theorem checked1629 : check 4000 c1629 = true := by decide

def original1630 : RawOriginal := C012.records[94]'(by decide)
theorem original_id1630 : original1630.index = 1630 := by decide

def c1630 : Contract := original1630.toContract.get (by decide)
theorem binding1630 : original1630.toContract = some c1630 := rfl

theorem checked1630 : check 4000 c1630 = true := by decide

def original1631 : RawOriginal := C012.records[95]'(by decide)
theorem original_id1631 : original1631.index = 1631 := by decide

def c1631 : Contract := original1631.toContract.get (by decide)
theorem binding1631 : original1631.toContract = some c1631 := rfl

theorem checked1631 : check 4000 c1631 = true := by decide

def original1632 : RawOriginal := C012.records[96]'(by decide)
theorem original_id1632 : original1632.index = 1632 := by decide

def c1632 : Contract := original1632.toContract.get (by decide)
theorem binding1632 : original1632.toContract = some c1632 := rfl

theorem checked1632 : check 4000 c1632 = true := by decide

def original1633 : RawOriginal := C012.records[97]'(by decide)
theorem original_id1633 : original1633.index = 1633 := by decide

def c1633 : Contract := original1633.toContract.get (by decide)
theorem binding1633 : original1633.toContract = some c1633 := rfl

theorem checked1633 : check 4000 c1633 = true := by decide

def original1634 : RawOriginal := C012.records[98]'(by decide)
theorem original_id1634 : original1634.index = 1634 := by decide

def c1634 : Contract := original1634.toContract.get (by decide)
theorem binding1634 : original1634.toContract = some c1634 := rfl

theorem checked1634 : check 4000 c1634 = true := by decide

def original1635 : RawOriginal := C012.records[99]'(by decide)
theorem original_id1635 : original1635.index = 1635 := by decide

def c1635 : Contract := original1635.toContract.get (by decide)
theorem binding1635 : original1635.toContract = some c1635 := rfl

theorem checked1635 : check 4000 c1635 = true := by decide

def original1636 : RawOriginal := C012.records[100]'(by decide)
theorem original_id1636 : original1636.index = 1636 := by decide

def c1636 : Contract := original1636.toContract.get (by decide)
theorem binding1636 : original1636.toContract = some c1636 := rfl

theorem checked1636 : check 4000 c1636 = true := by decide

def original1637 : RawOriginal := C012.records[101]'(by decide)
theorem original_id1637 : original1637.index = 1637 := by decide

def c1637 : Contract := original1637.toContract.get (by decide)
theorem binding1637 : original1637.toContract = some c1637 := rfl

theorem checked1637 : check 4000 c1637 = true := by decide

def records : List Certified := [
  ⟨1622, c1622, 4000, checked1622⟩,
  ⟨1623, c1623, 4000, checked1623⟩,
  ⟨1624, c1624, 4000, checked1624⟩,
  ⟨1625, c1625, 4000, checked1625⟩,
  ⟨1626, c1626, 4000, checked1626⟩,
  ⟨1627, c1627, 4000, checked1627⟩,
  ⟨1628, c1628, 4000, checked1628⟩,
  ⟨1629, c1629, 4000, checked1629⟩,
  ⟨1630, c1630, 4000, checked1630⟩,
  ⟨1631, c1631, 4000, checked1631⟩,
  ⟨1632, c1632, 4000, checked1632⟩,
  ⟨1633, c1633, 4000, checked1633⟩,
  ⟨1634, c1634, 4000, checked1634⟩,
  ⟨1635, c1635, 4000, checked1635⟩,
  ⟨1636, c1636, 4000, checked1636⟩,
  ⟨1637, c1637, 4000, checked1637⟩]

end PA215.ContractShards.Shard012Part5
