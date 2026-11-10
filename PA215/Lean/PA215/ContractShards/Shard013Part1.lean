import PA215.CertifiedContracts
import PA215.Census.C013
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard013Part1
open PA215.Contracts PA215.Census

def original1686 : RawOriginal := C013.records[22]'(by decide)
theorem original_id1686 : original1686.index = 1686 := by decide

def c1686 : Contract := original1686.toContract.get (by decide)
theorem binding1686 : original1686.toContract = some c1686 := rfl

theorem checked1686 : check 4000 c1686 = true := by decide

def original1687 : RawOriginal := C013.records[23]'(by decide)
theorem original_id1687 : original1687.index = 1687 := by decide

def c1687 : Contract := original1687.toContract.get (by decide)
theorem binding1687 : original1687.toContract = some c1687 := rfl

theorem checked1687 : check 4000 c1687 = true := by decide

def original1688 : RawOriginal := C013.records[24]'(by decide)
theorem original_id1688 : original1688.index = 1688 := by decide

def c1688 : Contract := original1688.toContract.get (by decide)
theorem binding1688 : original1688.toContract = some c1688 := rfl

theorem checked1688 : check 4000 c1688 = true := by decide

def original1689 : RawOriginal := C013.records[25]'(by decide)
theorem original_id1689 : original1689.index = 1689 := by decide

def c1689 : Contract := original1689.toContract.get (by decide)
theorem binding1689 : original1689.toContract = some c1689 := rfl

theorem checked1689 : check 4000 c1689 = true := by decide

def original1690 : RawOriginal := C013.records[26]'(by decide)
theorem original_id1690 : original1690.index = 1690 := by decide

def c1690 : Contract := original1690.toContract.get (by decide)
theorem binding1690 : original1690.toContract = some c1690 := rfl

theorem checked1690 : check 4000 c1690 = true := by decide

def original1691 : RawOriginal := C013.records[27]'(by decide)
theorem original_id1691 : original1691.index = 1691 := by decide

def c1691 : Contract := original1691.toContract.get (by decide)
theorem binding1691 : original1691.toContract = some c1691 := rfl

theorem checked1691 : check 4000 c1691 = true := by decide

def original1692 : RawOriginal := C013.records[28]'(by decide)
theorem original_id1692 : original1692.index = 1692 := by decide

def c1692 : Contract := original1692.toContract.get (by decide)
theorem binding1692 : original1692.toContract = some c1692 := rfl

theorem checked1692 : check 4000 c1692 = true := by decide

def original1693 : RawOriginal := C013.records[29]'(by decide)
theorem original_id1693 : original1693.index = 1693 := by decide

def c1693 : Contract := original1693.toContract.get (by decide)
theorem binding1693 : original1693.toContract = some c1693 := rfl

theorem checked1693 : check 4000 c1693 = true := by decide

def original1694 : RawOriginal := C013.records[30]'(by decide)
theorem original_id1694 : original1694.index = 1694 := by decide

def c1694 : Contract := original1694.toContract.get (by decide)
theorem binding1694 : original1694.toContract = some c1694 := rfl

theorem checked1694 : check 4000 c1694 = true := by decide

def original1695 : RawOriginal := C013.records[31]'(by decide)
theorem original_id1695 : original1695.index = 1695 := by decide

def c1695 : Contract := original1695.toContract.get (by decide)
theorem binding1695 : original1695.toContract = some c1695 := rfl

theorem checked1695 : check 4000 c1695 = true := by decide

def original1696 : RawOriginal := C013.records[32]'(by decide)
theorem original_id1696 : original1696.index = 1696 := by decide

def c1696 : Contract := original1696.toContract.get (by decide)
theorem binding1696 : original1696.toContract = some c1696 := rfl

theorem checked1696 : check 4000 c1696 = true := by decide

def original1697 : RawOriginal := C013.records[33]'(by decide)
theorem original_id1697 : original1697.index = 1697 := by decide

def c1697 : Contract := original1697.toContract.get (by decide)
theorem binding1697 : original1697.toContract = some c1697 := rfl

theorem checked1697 : check 4000 c1697 = true := by decide

def original1698 : RawOriginal := C013.records[34]'(by decide)
theorem original_id1698 : original1698.index = 1698 := by decide

def c1698 : Contract := original1698.toContract.get (by decide)
theorem binding1698 : original1698.toContract = some c1698 := rfl

theorem checked1698 : check 4000 c1698 = true := by decide

def original1699 : RawOriginal := C013.records[35]'(by decide)
theorem original_id1699 : original1699.index = 1699 := by decide

def c1699 : Contract := original1699.toContract.get (by decide)
theorem binding1699 : original1699.toContract = some c1699 := rfl

theorem checked1699 : check 4000 c1699 = true := by decide

def original1700 : RawOriginal := C013.records[36]'(by decide)
theorem original_id1700 : original1700.index = 1700 := by decide

def c1700 : Contract := original1700.toContract.get (by decide)
theorem binding1700 : original1700.toContract = some c1700 := rfl

theorem checked1700 : check 4000 c1700 = true := by decide

def original1701 : RawOriginal := C013.records[37]'(by decide)
theorem original_id1701 : original1701.index = 1701 := by decide

def c1701 : Contract := original1701.toContract.get (by decide)
theorem binding1701 : original1701.toContract = some c1701 := rfl

theorem checked1701 : check 4000 c1701 = true := by decide

def records : List Certified := [
  ⟨1686, c1686, 4000, checked1686⟩,
  ⟨1687, c1687, 4000, checked1687⟩,
  ⟨1688, c1688, 4000, checked1688⟩,
  ⟨1689, c1689, 4000, checked1689⟩,
  ⟨1690, c1690, 4000, checked1690⟩,
  ⟨1691, c1691, 4000, checked1691⟩,
  ⟨1692, c1692, 4000, checked1692⟩,
  ⟨1693, c1693, 4000, checked1693⟩,
  ⟨1694, c1694, 4000, checked1694⟩,
  ⟨1695, c1695, 4000, checked1695⟩,
  ⟨1696, c1696, 4000, checked1696⟩,
  ⟨1697, c1697, 4000, checked1697⟩,
  ⟨1698, c1698, 4000, checked1698⟩,
  ⟨1699, c1699, 4000, checked1699⟩,
  ⟨1700, c1700, 4000, checked1700⟩,
  ⟨1701, c1701, 4000, checked1701⟩]

end PA215.ContractShards.Shard013Part1
