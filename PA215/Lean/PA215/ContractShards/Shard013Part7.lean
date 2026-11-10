import PA215.CertifiedContracts
import PA215.Census.C013
import PA215.Census.C014
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard013Part7
open PA215.Contracts PA215.Census

def original1782 : RawOriginal := C013.records[118]'(by decide)
theorem original_id1782 : original1782.index = 1782 := by decide

def c1782 : Contract := original1782.toContract.get (by decide)
theorem binding1782 : original1782.toContract = some c1782 := rfl

theorem checked1782 : check 4000 c1782 = true := by decide

def original1783 : RawOriginal := C013.records[119]'(by decide)
theorem original_id1783 : original1783.index = 1783 := by decide

def c1783 : Contract := original1783.toContract.get (by decide)
theorem binding1783 : original1783.toContract = some c1783 := rfl

theorem checked1783 : check 4000 c1783 = true := by decide

def original1784 : RawOriginal := C013.records[120]'(by decide)
theorem original_id1784 : original1784.index = 1784 := by decide

def c1784 : Contract := original1784.toContract.get (by decide)
theorem binding1784 : original1784.toContract = some c1784 := rfl

theorem checked1784 : check 4000 c1784 = true := by decide

def original1785 : RawOriginal := C013.records[121]'(by decide)
theorem original_id1785 : original1785.index = 1785 := by decide

def c1785 : Contract := original1785.toContract.get (by decide)
theorem binding1785 : original1785.toContract = some c1785 := rfl

theorem checked1785 : check 4000 c1785 = true := by decide

def original1786 : RawOriginal := C013.records[122]'(by decide)
theorem original_id1786 : original1786.index = 1786 := by decide

def c1786 : Contract := original1786.toContract.get (by decide)
theorem binding1786 : original1786.toContract = some c1786 := rfl

theorem checked1786 : check 4000 c1786 = true := by decide

def original1787 : RawOriginal := C013.records[123]'(by decide)
theorem original_id1787 : original1787.index = 1787 := by decide

def c1787 : Contract := original1787.toContract.get (by decide)
theorem binding1787 : original1787.toContract = some c1787 := rfl

theorem checked1787 : check 4000 c1787 = true := by decide

def original1788 : RawOriginal := C013.records[124]'(by decide)
theorem original_id1788 : original1788.index = 1788 := by decide

def c1788 : Contract := original1788.toContract.get (by decide)
theorem binding1788 : original1788.toContract = some c1788 := rfl

theorem checked1788 : check 4000 c1788 = true := by decide

def original1789 : RawOriginal := C013.records[125]'(by decide)
theorem original_id1789 : original1789.index = 1789 := by decide

def c1789 : Contract := original1789.toContract.get (by decide)
theorem binding1789 : original1789.toContract = some c1789 := rfl

theorem checked1789 : check 4000 c1789 = true := by decide

def original1790 : RawOriginal := C013.records[126]'(by decide)
theorem original_id1790 : original1790.index = 1790 := by decide

def c1790 : Contract := original1790.toContract.get (by decide)
theorem binding1790 : original1790.toContract = some c1790 := rfl

theorem checked1790 : check 4000 c1790 = true := by decide

def original1791 : RawOriginal := C013.records[127]'(by decide)
theorem original_id1791 : original1791.index = 1791 := by decide

def c1791 : Contract := original1791.toContract.get (by decide)
theorem binding1791 : original1791.toContract = some c1791 := rfl

theorem checked1791 : check 4000 c1791 = true := by decide

def original1792 : RawOriginal := C014.records[0]'(by decide)
theorem original_id1792 : original1792.index = 1792 := by decide

def c1792 : Contract := original1792.toContract.get (by decide)
theorem binding1792 : original1792.toContract = some c1792 := rfl

theorem checked1792 : check 4000 c1792 = true := by decide

def original1793 : RawOriginal := C014.records[1]'(by decide)
theorem original_id1793 : original1793.index = 1793 := by decide

def c1793 : Contract := original1793.toContract.get (by decide)
theorem binding1793 : original1793.toContract = some c1793 := rfl

theorem checked1793 : check 4000 c1793 = true := by decide

def original1794 : RawOriginal := C014.records[2]'(by decide)
theorem original_id1794 : original1794.index = 1794 := by decide

def c1794 : Contract := original1794.toContract.get (by decide)
theorem binding1794 : original1794.toContract = some c1794 := rfl

theorem checked1794 : check 4000 c1794 = true := by decide

def original1795 : RawOriginal := C014.records[3]'(by decide)
theorem original_id1795 : original1795.index = 1795 := by decide

def c1795 : Contract := original1795.toContract.get (by decide)
theorem binding1795 : original1795.toContract = some c1795 := rfl

theorem checked1795 : check 4000 c1795 = true := by decide

def original1796 : RawOriginal := C014.records[4]'(by decide)
theorem original_id1796 : original1796.index = 1796 := by decide

def c1796 : Contract := original1796.toContract.get (by decide)
theorem binding1796 : original1796.toContract = some c1796 := rfl

theorem checked1796 : check 4000 c1796 = true := by decide

def original1797 : RawOriginal := C014.records[5]'(by decide)
theorem original_id1797 : original1797.index = 1797 := by decide

def c1797 : Contract := original1797.toContract.get (by decide)
theorem binding1797 : original1797.toContract = some c1797 := rfl

theorem checked1797 : check 4000 c1797 = true := by decide

def records : List Certified := [
  ⟨1782, c1782, 4000, checked1782⟩,
  ⟨1783, c1783, 4000, checked1783⟩,
  ⟨1784, c1784, 4000, checked1784⟩,
  ⟨1785, c1785, 4000, checked1785⟩,
  ⟨1786, c1786, 4000, checked1786⟩,
  ⟨1787, c1787, 4000, checked1787⟩,
  ⟨1788, c1788, 4000, checked1788⟩,
  ⟨1789, c1789, 4000, checked1789⟩,
  ⟨1790, c1790, 4000, checked1790⟩,
  ⟨1791, c1791, 4000, checked1791⟩,
  ⟨1792, c1792, 4000, checked1792⟩,
  ⟨1793, c1793, 4000, checked1793⟩,
  ⟨1794, c1794, 4000, checked1794⟩,
  ⟨1795, c1795, 4000, checked1795⟩,
  ⟨1796, c1796, 4000, checked1796⟩,
  ⟨1797, c1797, 4000, checked1797⟩]

end PA215.ContractShards.Shard013Part7
