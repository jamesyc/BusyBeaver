import PA215.CertifiedContracts
import PA215.Census.C013
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard013Part4
open PA215.Contracts PA215.Census

def original1734 : RawOriginal := C013.records[70]'(by decide)
theorem original_id1734 : original1734.index = 1734 := by decide

def c1734 : Contract := original1734.toContract.get (by decide)
theorem binding1734 : original1734.toContract = some c1734 := rfl

theorem checked1734 : check 4000 c1734 = true := by decide

def original1735 : RawOriginal := C013.records[71]'(by decide)
theorem original_id1735 : original1735.index = 1735 := by decide

def c1735 : Contract := original1735.toContract.get (by decide)
theorem binding1735 : original1735.toContract = some c1735 := rfl

theorem checked1735 : check 4000 c1735 = true := by decide

def original1736 : RawOriginal := C013.records[72]'(by decide)
theorem original_id1736 : original1736.index = 1736 := by decide

def c1736 : Contract := original1736.toContract.get (by decide)
theorem binding1736 : original1736.toContract = some c1736 := rfl

theorem checked1736 : check 4000 c1736 = true := by decide

def original1737 : RawOriginal := C013.records[73]'(by decide)
theorem original_id1737 : original1737.index = 1737 := by decide

def c1737 : Contract := original1737.toContract.get (by decide)
theorem binding1737 : original1737.toContract = some c1737 := rfl

theorem checked1737 : check 4000 c1737 = true := by decide

def original1738 : RawOriginal := C013.records[74]'(by decide)
theorem original_id1738 : original1738.index = 1738 := by decide

def c1738 : Contract := original1738.toContract.get (by decide)
theorem binding1738 : original1738.toContract = some c1738 := rfl

theorem checked1738 : check 4000 c1738 = true := by decide

def original1739 : RawOriginal := C013.records[75]'(by decide)
theorem original_id1739 : original1739.index = 1739 := by decide

def c1739 : Contract := original1739.toContract.get (by decide)
theorem binding1739 : original1739.toContract = some c1739 := rfl

theorem checked1739 : check 4000 c1739 = true := by decide

def original1740 : RawOriginal := C013.records[76]'(by decide)
theorem original_id1740 : original1740.index = 1740 := by decide

def c1740 : Contract := original1740.toContract.get (by decide)
theorem binding1740 : original1740.toContract = some c1740 := rfl

theorem checked1740 : check 4000 c1740 = true := by decide

def original1741 : RawOriginal := C013.records[77]'(by decide)
theorem original_id1741 : original1741.index = 1741 := by decide

def c1741 : Contract := original1741.toContract.get (by decide)
theorem binding1741 : original1741.toContract = some c1741 := rfl

theorem checked1741 : check 4000 c1741 = true := by decide

def original1742 : RawOriginal := C013.records[78]'(by decide)
theorem original_id1742 : original1742.index = 1742 := by decide

def c1742 : Contract := original1742.toContract.get (by decide)
theorem binding1742 : original1742.toContract = some c1742 := rfl

theorem checked1742 : check 4000 c1742 = true := by decide

def original1743 : RawOriginal := C013.records[79]'(by decide)
theorem original_id1743 : original1743.index = 1743 := by decide

def c1743 : Contract := original1743.toContract.get (by decide)
theorem binding1743 : original1743.toContract = some c1743 := rfl

theorem checked1743 : check 4000 c1743 = true := by decide

def original1744 : RawOriginal := C013.records[80]'(by decide)
theorem original_id1744 : original1744.index = 1744 := by decide

def c1744 : Contract := original1744.toContract.get (by decide)
theorem binding1744 : original1744.toContract = some c1744 := rfl

theorem checked1744 : check 4000 c1744 = true := by decide

def original1745 : RawOriginal := C013.records[81]'(by decide)
theorem original_id1745 : original1745.index = 1745 := by decide

def c1745 : Contract := original1745.toContract.get (by decide)
theorem binding1745 : original1745.toContract = some c1745 := rfl

theorem checked1745 : check 4000 c1745 = true := by decide

def original1746 : RawOriginal := C013.records[82]'(by decide)
theorem original_id1746 : original1746.index = 1746 := by decide

def c1746 : Contract := original1746.toContract.get (by decide)
theorem binding1746 : original1746.toContract = some c1746 := rfl

theorem checked1746 : check 4000 c1746 = true := by decide

def original1747 : RawOriginal := C013.records[83]'(by decide)
theorem original_id1747 : original1747.index = 1747 := by decide

def c1747 : Contract := original1747.toContract.get (by decide)
theorem binding1747 : original1747.toContract = some c1747 := rfl

theorem checked1747 : check 4000 c1747 = true := by decide

def original1748 : RawOriginal := C013.records[84]'(by decide)
theorem original_id1748 : original1748.index = 1748 := by decide

def c1748 : Contract := original1748.toContract.get (by decide)
theorem binding1748 : original1748.toContract = some c1748 := rfl

theorem checked1748 : check 4000 c1748 = true := by decide

def original1749 : RawOriginal := C013.records[85]'(by decide)
theorem original_id1749 : original1749.index = 1749 := by decide

def c1749 : Contract := original1749.toContract.get (by decide)
theorem binding1749 : original1749.toContract = some c1749 := rfl

theorem checked1749 : check 4000 c1749 = true := by decide

def records : List Certified := [
  ⟨1734, c1734, 4000, checked1734⟩,
  ⟨1735, c1735, 4000, checked1735⟩,
  ⟨1736, c1736, 4000, checked1736⟩,
  ⟨1737, c1737, 4000, checked1737⟩,
  ⟨1738, c1738, 4000, checked1738⟩,
  ⟨1739, c1739, 4000, checked1739⟩,
  ⟨1740, c1740, 4000, checked1740⟩,
  ⟨1741, c1741, 4000, checked1741⟩,
  ⟨1742, c1742, 4000, checked1742⟩,
  ⟨1743, c1743, 4000, checked1743⟩,
  ⟨1744, c1744, 4000, checked1744⟩,
  ⟨1745, c1745, 4000, checked1745⟩,
  ⟨1746, c1746, 4000, checked1746⟩,
  ⟨1747, c1747, 4000, checked1747⟩,
  ⟨1748, c1748, 4000, checked1748⟩,
  ⟨1749, c1749, 4000, checked1749⟩]

end PA215.ContractShards.Shard013Part4
