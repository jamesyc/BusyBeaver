import PA215.CertifiedContracts
import PA215.Census.C014
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard014Part2
open PA215.Contracts PA215.Census

def original1830 : RawOriginal := C014.records[38]'(by decide)
theorem original_id1830 : original1830.index = 1830 := by decide

def c1830 : Contract := original1830.toContract.get (by decide)
theorem binding1830 : original1830.toContract = some c1830 := rfl

theorem checked1830 : check 4000 c1830 = true := by decide

def original1831 : RawOriginal := C014.records[39]'(by decide)
theorem original_id1831 : original1831.index = 1831 := by decide

def c1831 : Contract := original1831.toContract.get (by decide)
theorem binding1831 : original1831.toContract = some c1831 := rfl

theorem checked1831 : check 4000 c1831 = true := by decide

def original1832 : RawOriginal := C014.records[40]'(by decide)
theorem original_id1832 : original1832.index = 1832 := by decide

def c1832 : Contract := original1832.toContract.get (by decide)
theorem binding1832 : original1832.toContract = some c1832 := rfl

theorem checked1832 : check 4000 c1832 = true := by decide

def original1833 : RawOriginal := C014.records[41]'(by decide)
theorem original_id1833 : original1833.index = 1833 := by decide

def c1833 : Contract := original1833.toContract.get (by decide)
theorem binding1833 : original1833.toContract = some c1833 := rfl

theorem checked1833 : check 4000 c1833 = true := by decide

def original1834 : RawOriginal := C014.records[42]'(by decide)
theorem original_id1834 : original1834.index = 1834 := by decide

def c1834 : Contract := original1834.toContract.get (by decide)
theorem binding1834 : original1834.toContract = some c1834 := rfl

theorem checked1834 : check 4000 c1834 = true := by decide

def original1835 : RawOriginal := C014.records[43]'(by decide)
theorem original_id1835 : original1835.index = 1835 := by decide

def c1835 : Contract := original1835.toContract.get (by decide)
theorem binding1835 : original1835.toContract = some c1835 := rfl

theorem checked1835 : check 4000 c1835 = true := by decide

def original1836 : RawOriginal := C014.records[44]'(by decide)
theorem original_id1836 : original1836.index = 1836 := by decide

def c1836 : Contract := original1836.toContract.get (by decide)
theorem binding1836 : original1836.toContract = some c1836 := rfl

theorem checked1836 : check 4000 c1836 = true := by decide

def original1837 : RawOriginal := C014.records[45]'(by decide)
theorem original_id1837 : original1837.index = 1837 := by decide

def c1837 : Contract := original1837.toContract.get (by decide)
theorem binding1837 : original1837.toContract = some c1837 := rfl

theorem checked1837 : check 4000 c1837 = true := by decide

def original1838 : RawOriginal := C014.records[46]'(by decide)
theorem original_id1838 : original1838.index = 1838 := by decide

def c1838 : Contract := original1838.toContract.get (by decide)
theorem binding1838 : original1838.toContract = some c1838 := rfl

theorem checked1838 : check 4000 c1838 = true := by decide

def original1839 : RawOriginal := C014.records[47]'(by decide)
theorem original_id1839 : original1839.index = 1839 := by decide

def c1839 : Contract := original1839.toContract.get (by decide)
theorem binding1839 : original1839.toContract = some c1839 := rfl

theorem checked1839 : check 4000 c1839 = true := by decide

def original1840 : RawOriginal := C014.records[48]'(by decide)
theorem original_id1840 : original1840.index = 1840 := by decide

def c1840 : Contract := original1840.toContract.get (by decide)
theorem binding1840 : original1840.toContract = some c1840 := rfl

theorem checked1840 : check 4000 c1840 = true := by decide

def original1841 : RawOriginal := C014.records[49]'(by decide)
theorem original_id1841 : original1841.index = 1841 := by decide

def c1841 : Contract := original1841.toContract.get (by decide)
theorem binding1841 : original1841.toContract = some c1841 := rfl

theorem checked1841 : check 4000 c1841 = true := by decide

def original1842 : RawOriginal := C014.records[50]'(by decide)
theorem original_id1842 : original1842.index = 1842 := by decide

def c1842 : Contract := original1842.toContract.get (by decide)
theorem binding1842 : original1842.toContract = some c1842 := rfl

theorem checked1842 : check 4000 c1842 = true := by decide

def original1843 : RawOriginal := C014.records[51]'(by decide)
theorem original_id1843 : original1843.index = 1843 := by decide

def c1843 : Contract := original1843.toContract.get (by decide)
theorem binding1843 : original1843.toContract = some c1843 := rfl

theorem checked1843 : check 4000 c1843 = true := by decide

def original1844 : RawOriginal := C014.records[52]'(by decide)
theorem original_id1844 : original1844.index = 1844 := by decide

def c1844 : Contract := original1844.toContract.get (by decide)
theorem binding1844 : original1844.toContract = some c1844 := rfl

theorem checked1844 : check 4000 c1844 = true := by decide

def original1845 : RawOriginal := C014.records[53]'(by decide)
theorem original_id1845 : original1845.index = 1845 := by decide

def c1845 : Contract := original1845.toContract.get (by decide)
theorem binding1845 : original1845.toContract = some c1845 := rfl

theorem checked1845 : check 4000 c1845 = true := by decide

def records : List Certified := [
  ⟨1830, c1830, 4000, checked1830⟩,
  ⟨1831, c1831, 4000, checked1831⟩,
  ⟨1832, c1832, 4000, checked1832⟩,
  ⟨1833, c1833, 4000, checked1833⟩,
  ⟨1834, c1834, 4000, checked1834⟩,
  ⟨1835, c1835, 4000, checked1835⟩,
  ⟨1836, c1836, 4000, checked1836⟩,
  ⟨1837, c1837, 4000, checked1837⟩,
  ⟨1838, c1838, 4000, checked1838⟩,
  ⟨1839, c1839, 4000, checked1839⟩,
  ⟨1840, c1840, 4000, checked1840⟩,
  ⟨1841, c1841, 4000, checked1841⟩,
  ⟨1842, c1842, 4000, checked1842⟩,
  ⟨1843, c1843, 4000, checked1843⟩,
  ⟨1844, c1844, 4000, checked1844⟩,
  ⟨1845, c1845, 4000, checked1845⟩]

end PA215.ContractShards.Shard014Part2
