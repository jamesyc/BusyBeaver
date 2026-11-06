import PA215.CertifiedContracts
import PA215.Census.C014
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard014Part0
open PA215.Contracts PA215.Census

def original1798 : RawOriginal := C014.records[6]'(by decide)
theorem original_id1798 : original1798.index = 1798 := by decide

def c1798 : Contract := original1798.toContract.get (by decide)
theorem binding1798 : original1798.toContract = some c1798 := rfl

theorem checked1798 : check 4000 c1798 = true := by decide

def original1799 : RawOriginal := C014.records[7]'(by decide)
theorem original_id1799 : original1799.index = 1799 := by decide

def c1799 : Contract := original1799.toContract.get (by decide)
theorem binding1799 : original1799.toContract = some c1799 := rfl

theorem checked1799 : check 4000 c1799 = true := by decide

def original1800 : RawOriginal := C014.records[8]'(by decide)
theorem original_id1800 : original1800.index = 1800 := by decide

def c1800 : Contract := original1800.toContract.get (by decide)
theorem binding1800 : original1800.toContract = some c1800 := rfl

theorem checked1800 : check 4000 c1800 = true := by decide

def original1801 : RawOriginal := C014.records[9]'(by decide)
theorem original_id1801 : original1801.index = 1801 := by decide

def c1801 : Contract := original1801.toContract.get (by decide)
theorem binding1801 : original1801.toContract = some c1801 := rfl

theorem checked1801 : check 4000 c1801 = true := by decide

def original1802 : RawOriginal := C014.records[10]'(by decide)
theorem original_id1802 : original1802.index = 1802 := by decide

def c1802 : Contract := original1802.toContract.get (by decide)
theorem binding1802 : original1802.toContract = some c1802 := rfl

theorem checked1802 : check 4000 c1802 = true := by decide

def original1803 : RawOriginal := C014.records[11]'(by decide)
theorem original_id1803 : original1803.index = 1803 := by decide

def c1803 : Contract := original1803.toContract.get (by decide)
theorem binding1803 : original1803.toContract = some c1803 := rfl

theorem checked1803 : check 4000 c1803 = true := by decide

def original1804 : RawOriginal := C014.records[12]'(by decide)
theorem original_id1804 : original1804.index = 1804 := by decide

def c1804 : Contract := original1804.toContract.get (by decide)
theorem binding1804 : original1804.toContract = some c1804 := rfl

theorem checked1804 : check 4000 c1804 = true := by decide

def original1805 : RawOriginal := C014.records[13]'(by decide)
theorem original_id1805 : original1805.index = 1805 := by decide

def c1805 : Contract := original1805.toContract.get (by decide)
theorem binding1805 : original1805.toContract = some c1805 := rfl

theorem checked1805 : check 4000 c1805 = true := by decide

def original1806 : RawOriginal := C014.records[14]'(by decide)
theorem original_id1806 : original1806.index = 1806 := by decide

def c1806 : Contract := original1806.toContract.get (by decide)
theorem binding1806 : original1806.toContract = some c1806 := rfl

theorem checked1806 : check 4000 c1806 = true := by decide

def original1807 : RawOriginal := C014.records[15]'(by decide)
theorem original_id1807 : original1807.index = 1807 := by decide

def c1807 : Contract := original1807.toContract.get (by decide)
theorem binding1807 : original1807.toContract = some c1807 := rfl

theorem checked1807 : check 4000 c1807 = true := by decide

def original1808 : RawOriginal := C014.records[16]'(by decide)
theorem original_id1808 : original1808.index = 1808 := by decide

def c1808 : Contract := original1808.toContract.get (by decide)
theorem binding1808 : original1808.toContract = some c1808 := rfl

theorem checked1808 : check 4000 c1808 = true := by decide

def original1809 : RawOriginal := C014.records[17]'(by decide)
theorem original_id1809 : original1809.index = 1809 := by decide

def c1809 : Contract := original1809.toContract.get (by decide)
theorem binding1809 : original1809.toContract = some c1809 := rfl

theorem checked1809 : check 4000 c1809 = true := by decide

def original1810 : RawOriginal := C014.records[18]'(by decide)
theorem original_id1810 : original1810.index = 1810 := by decide

def c1810 : Contract := original1810.toContract.get (by decide)
theorem binding1810 : original1810.toContract = some c1810 := rfl

theorem checked1810 : check 4000 c1810 = true := by decide

def original1811 : RawOriginal := C014.records[19]'(by decide)
theorem original_id1811 : original1811.index = 1811 := by decide

def c1811 : Contract := original1811.toContract.get (by decide)
theorem binding1811 : original1811.toContract = some c1811 := rfl

theorem checked1811 : check 4000 c1811 = true := by decide

def original1812 : RawOriginal := C014.records[20]'(by decide)
theorem original_id1812 : original1812.index = 1812 := by decide

def c1812 : Contract := original1812.toContract.get (by decide)
theorem binding1812 : original1812.toContract = some c1812 := rfl

theorem checked1812 : check 4000 c1812 = true := by decide

def original1813 : RawOriginal := C014.records[21]'(by decide)
theorem original_id1813 : original1813.index = 1813 := by decide

def c1813 : Contract := original1813.toContract.get (by decide)
theorem binding1813 : original1813.toContract = some c1813 := rfl

theorem checked1813 : check 4000 c1813 = true := by decide

def records : List Certified := [
  ⟨1798, c1798, 4000, checked1798⟩,
  ⟨1799, c1799, 4000, checked1799⟩,
  ⟨1800, c1800, 4000, checked1800⟩,
  ⟨1801, c1801, 4000, checked1801⟩,
  ⟨1802, c1802, 4000, checked1802⟩,
  ⟨1803, c1803, 4000, checked1803⟩,
  ⟨1804, c1804, 4000, checked1804⟩,
  ⟨1805, c1805, 4000, checked1805⟩,
  ⟨1806, c1806, 4000, checked1806⟩,
  ⟨1807, c1807, 4000, checked1807⟩,
  ⟨1808, c1808, 4000, checked1808⟩,
  ⟨1809, c1809, 4000, checked1809⟩,
  ⟨1810, c1810, 4000, checked1810⟩,
  ⟨1811, c1811, 4000, checked1811⟩,
  ⟨1812, c1812, 4000, checked1812⟩,
  ⟨1813, c1813, 4000, checked1813⟩]

end PA215.ContractShards.Shard014Part0
