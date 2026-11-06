import PA215.CertifiedContracts
import PA215.Census.C014
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard014Part1
open PA215.Contracts PA215.Census

def original1814 : RawOriginal := C014.records[22]'(by decide)
theorem original_id1814 : original1814.index = 1814 := by decide

def c1814 : Contract := original1814.toContract.get (by decide)
theorem binding1814 : original1814.toContract = some c1814 := rfl

theorem checked1814 : check 4000 c1814 = true := by decide

def original1815 : RawOriginal := C014.records[23]'(by decide)
theorem original_id1815 : original1815.index = 1815 := by decide

def c1815 : Contract := original1815.toContract.get (by decide)
theorem binding1815 : original1815.toContract = some c1815 := rfl

theorem checked1815 : check 4000 c1815 = true := by decide

def original1816 : RawOriginal := C014.records[24]'(by decide)
theorem original_id1816 : original1816.index = 1816 := by decide

def c1816 : Contract := original1816.toContract.get (by decide)
theorem binding1816 : original1816.toContract = some c1816 := rfl

theorem checked1816 : check 4000 c1816 = true := by decide

def original1817 : RawOriginal := C014.records[25]'(by decide)
theorem original_id1817 : original1817.index = 1817 := by decide

def c1817 : Contract := original1817.toContract.get (by decide)
theorem binding1817 : original1817.toContract = some c1817 := rfl

theorem checked1817 : check 4000 c1817 = true := by decide

def original1818 : RawOriginal := C014.records[26]'(by decide)
theorem original_id1818 : original1818.index = 1818 := by decide

def c1818 : Contract := original1818.toContract.get (by decide)
theorem binding1818 : original1818.toContract = some c1818 := rfl

theorem checked1818 : check 4000 c1818 = true := by decide

def original1819 : RawOriginal := C014.records[27]'(by decide)
theorem original_id1819 : original1819.index = 1819 := by decide

def c1819 : Contract := original1819.toContract.get (by decide)
theorem binding1819 : original1819.toContract = some c1819 := rfl

theorem checked1819 : check 4000 c1819 = true := by decide

def original1820 : RawOriginal := C014.records[28]'(by decide)
theorem original_id1820 : original1820.index = 1820 := by decide

def c1820 : Contract := original1820.toContract.get (by decide)
theorem binding1820 : original1820.toContract = some c1820 := rfl

theorem checked1820 : check 4000 c1820 = true := by decide

def original1821 : RawOriginal := C014.records[29]'(by decide)
theorem original_id1821 : original1821.index = 1821 := by decide

def c1821 : Contract := original1821.toContract.get (by decide)
theorem binding1821 : original1821.toContract = some c1821 := rfl

theorem checked1821 : check 4000 c1821 = true := by decide

def original1822 : RawOriginal := C014.records[30]'(by decide)
theorem original_id1822 : original1822.index = 1822 := by decide

def c1822 : Contract := original1822.toContract.get (by decide)
theorem binding1822 : original1822.toContract = some c1822 := rfl

theorem checked1822 : check 4000 c1822 = true := by decide

def original1823 : RawOriginal := C014.records[31]'(by decide)
theorem original_id1823 : original1823.index = 1823 := by decide

def c1823 : Contract := original1823.toContract.get (by decide)
theorem binding1823 : original1823.toContract = some c1823 := rfl

theorem checked1823 : check 4000 c1823 = true := by decide

def original1824 : RawOriginal := C014.records[32]'(by decide)
theorem original_id1824 : original1824.index = 1824 := by decide

def c1824 : Contract := original1824.toContract.get (by decide)
theorem binding1824 : original1824.toContract = some c1824 := rfl

theorem checked1824 : check 4000 c1824 = true := by decide

def original1825 : RawOriginal := C014.records[33]'(by decide)
theorem original_id1825 : original1825.index = 1825 := by decide

def c1825 : Contract := original1825.toContract.get (by decide)
theorem binding1825 : original1825.toContract = some c1825 := rfl

theorem checked1825 : check 4000 c1825 = true := by decide

def original1826 : RawOriginal := C014.records[34]'(by decide)
theorem original_id1826 : original1826.index = 1826 := by decide

def c1826 : Contract := original1826.toContract.get (by decide)
theorem binding1826 : original1826.toContract = some c1826 := rfl

theorem checked1826 : check 4000 c1826 = true := by decide

def original1827 : RawOriginal := C014.records[35]'(by decide)
theorem original_id1827 : original1827.index = 1827 := by decide

def c1827 : Contract := original1827.toContract.get (by decide)
theorem binding1827 : original1827.toContract = some c1827 := rfl

theorem checked1827 : check 4000 c1827 = true := by decide

def original1828 : RawOriginal := C014.records[36]'(by decide)
theorem original_id1828 : original1828.index = 1828 := by decide

def c1828 : Contract := original1828.toContract.get (by decide)
theorem binding1828 : original1828.toContract = some c1828 := rfl

theorem checked1828 : check 4000 c1828 = true := by decide

def original1829 : RawOriginal := C014.records[37]'(by decide)
theorem original_id1829 : original1829.index = 1829 := by decide

def c1829 : Contract := original1829.toContract.get (by decide)
theorem binding1829 : original1829.toContract = some c1829 := rfl

theorem checked1829 : check 4000 c1829 = true := by decide

def records : List Certified := [
  ⟨1814, c1814, 4000, checked1814⟩,
  ⟨1815, c1815, 4000, checked1815⟩,
  ⟨1816, c1816, 4000, checked1816⟩,
  ⟨1817, c1817, 4000, checked1817⟩,
  ⟨1818, c1818, 4000, checked1818⟩,
  ⟨1819, c1819, 4000, checked1819⟩,
  ⟨1820, c1820, 4000, checked1820⟩,
  ⟨1821, c1821, 4000, checked1821⟩,
  ⟨1822, c1822, 4000, checked1822⟩,
  ⟨1823, c1823, 4000, checked1823⟩,
  ⟨1824, c1824, 4000, checked1824⟩,
  ⟨1825, c1825, 4000, checked1825⟩,
  ⟨1826, c1826, 4000, checked1826⟩,
  ⟨1827, c1827, 4000, checked1827⟩,
  ⟨1828, c1828, 4000, checked1828⟩,
  ⟨1829, c1829, 4000, checked1829⟩]

end PA215.ContractShards.Shard014Part1
