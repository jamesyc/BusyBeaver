import PA215.CertifiedContracts
import PA215.Census.C013
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard013Part5
open PA215.Contracts PA215.Census

def original1750 : RawOriginal := C013.records[86]'(by decide)
theorem original_id1750 : original1750.index = 1750 := by decide

def c1750 : Contract := original1750.toContract.get (by decide)
theorem binding1750 : original1750.toContract = some c1750 := rfl

theorem checked1750 : check 4000 c1750 = true := by decide

def original1751 : RawOriginal := C013.records[87]'(by decide)
theorem original_id1751 : original1751.index = 1751 := by decide

def c1751 : Contract := original1751.toContract.get (by decide)
theorem binding1751 : original1751.toContract = some c1751 := rfl

theorem checked1751 : check 4000 c1751 = true := by decide

def original1752 : RawOriginal := C013.records[88]'(by decide)
theorem original_id1752 : original1752.index = 1752 := by decide

def c1752 : Contract := original1752.toContract.get (by decide)
theorem binding1752 : original1752.toContract = some c1752 := rfl

theorem checked1752 : check 4000 c1752 = true := by decide

def original1753 : RawOriginal := C013.records[89]'(by decide)
theorem original_id1753 : original1753.index = 1753 := by decide

def c1753 : Contract := original1753.toContract.get (by decide)
theorem binding1753 : original1753.toContract = some c1753 := rfl

theorem checked1753 : check 4000 c1753 = true := by decide

def original1754 : RawOriginal := C013.records[90]'(by decide)
theorem original_id1754 : original1754.index = 1754 := by decide

def c1754 : Contract := original1754.toContract.get (by decide)
theorem binding1754 : original1754.toContract = some c1754 := rfl

theorem checked1754 : check 4000 c1754 = true := by decide

def original1755 : RawOriginal := C013.records[91]'(by decide)
theorem original_id1755 : original1755.index = 1755 := by decide

def c1755 : Contract := original1755.toContract.get (by decide)
theorem binding1755 : original1755.toContract = some c1755 := rfl

theorem checked1755 : check 4000 c1755 = true := by decide

def original1756 : RawOriginal := C013.records[92]'(by decide)
theorem original_id1756 : original1756.index = 1756 := by decide

def c1756 : Contract := original1756.toContract.get (by decide)
theorem binding1756 : original1756.toContract = some c1756 := rfl

theorem checked1756 : check 4000 c1756 = true := by decide

def original1757 : RawOriginal := C013.records[93]'(by decide)
theorem original_id1757 : original1757.index = 1757 := by decide

def c1757 : Contract := original1757.toContract.get (by decide)
theorem binding1757 : original1757.toContract = some c1757 := rfl

theorem checked1757 : check 4000 c1757 = true := by decide

def original1758 : RawOriginal := C013.records[94]'(by decide)
theorem original_id1758 : original1758.index = 1758 := by decide

def c1758 : Contract := original1758.toContract.get (by decide)
theorem binding1758 : original1758.toContract = some c1758 := rfl

theorem checked1758 : check 4000 c1758 = true := by decide

def original1759 : RawOriginal := C013.records[95]'(by decide)
theorem original_id1759 : original1759.index = 1759 := by decide

def c1759 : Contract := original1759.toContract.get (by decide)
theorem binding1759 : original1759.toContract = some c1759 := rfl

theorem checked1759 : check 4000 c1759 = true := by decide

def original1760 : RawOriginal := C013.records[96]'(by decide)
theorem original_id1760 : original1760.index = 1760 := by decide

def c1760 : Contract := original1760.toContract.get (by decide)
theorem binding1760 : original1760.toContract = some c1760 := rfl

theorem checked1760 : check 4000 c1760 = true := by decide

def original1761 : RawOriginal := C013.records[97]'(by decide)
theorem original_id1761 : original1761.index = 1761 := by decide

def c1761 : Contract := original1761.toContract.get (by decide)
theorem binding1761 : original1761.toContract = some c1761 := rfl

theorem checked1761 : check 4000 c1761 = true := by decide

def original1762 : RawOriginal := C013.records[98]'(by decide)
theorem original_id1762 : original1762.index = 1762 := by decide

def c1762 : Contract := original1762.toContract.get (by decide)
theorem binding1762 : original1762.toContract = some c1762 := rfl

theorem checked1762 : check 4000 c1762 = true := by decide

def original1763 : RawOriginal := C013.records[99]'(by decide)
theorem original_id1763 : original1763.index = 1763 := by decide

def c1763 : Contract := original1763.toContract.get (by decide)
theorem binding1763 : original1763.toContract = some c1763 := rfl

theorem checked1763 : check 4000 c1763 = true := by decide

def original1764 : RawOriginal := C013.records[100]'(by decide)
theorem original_id1764 : original1764.index = 1764 := by decide

def c1764 : Contract := original1764.toContract.get (by decide)
theorem binding1764 : original1764.toContract = some c1764 := rfl

theorem checked1764 : check 4000 c1764 = true := by decide

def original1765 : RawOriginal := C013.records[101]'(by decide)
theorem original_id1765 : original1765.index = 1765 := by decide

def c1765 : Contract := original1765.toContract.get (by decide)
theorem binding1765 : original1765.toContract = some c1765 := rfl

theorem checked1765 : check 4000 c1765 = true := by decide

def records : List Certified := [
  ⟨1750, c1750, 4000, checked1750⟩,
  ⟨1751, c1751, 4000, checked1751⟩,
  ⟨1752, c1752, 4000, checked1752⟩,
  ⟨1753, c1753, 4000, checked1753⟩,
  ⟨1754, c1754, 4000, checked1754⟩,
  ⟨1755, c1755, 4000, checked1755⟩,
  ⟨1756, c1756, 4000, checked1756⟩,
  ⟨1757, c1757, 4000, checked1757⟩,
  ⟨1758, c1758, 4000, checked1758⟩,
  ⟨1759, c1759, 4000, checked1759⟩,
  ⟨1760, c1760, 4000, checked1760⟩,
  ⟨1761, c1761, 4000, checked1761⟩,
  ⟨1762, c1762, 4000, checked1762⟩,
  ⟨1763, c1763, 4000, checked1763⟩,
  ⟨1764, c1764, 4000, checked1764⟩,
  ⟨1765, c1765, 4000, checked1765⟩]

end PA215.ContractShards.Shard013Part5
