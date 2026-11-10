import PA215.CertifiedContracts
import PA215.Census.C014
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard014Part3
open PA215.Contracts PA215.Census

def original1846 : RawOriginal := C014.records[54]'(by decide)
theorem original_id1846 : original1846.index = 1846 := by decide

def c1846 : Contract := original1846.toContract.get (by decide)
theorem binding1846 : original1846.toContract = some c1846 := rfl

theorem checked1846 : check 4000 c1846 = true := by decide

def original1847 : RawOriginal := C014.records[55]'(by decide)
theorem original_id1847 : original1847.index = 1847 := by decide

def c1847 : Contract := original1847.toContract.get (by decide)
theorem binding1847 : original1847.toContract = some c1847 := rfl

theorem checked1847 : check 4000 c1847 = true := by decide

def original1848 : RawOriginal := C014.records[56]'(by decide)
theorem original_id1848 : original1848.index = 1848 := by decide

def c1848 : Contract := original1848.toContract.get (by decide)
theorem binding1848 : original1848.toContract = some c1848 := rfl

theorem checked1848 : check 4000 c1848 = true := by decide

def original1849 : RawOriginal := C014.records[57]'(by decide)
theorem original_id1849 : original1849.index = 1849 := by decide

def c1849 : Contract := original1849.toContract.get (by decide)
theorem binding1849 : original1849.toContract = some c1849 := rfl

theorem checked1849 : check 4000 c1849 = true := by decide

def original1850 : RawOriginal := C014.records[58]'(by decide)
theorem original_id1850 : original1850.index = 1850 := by decide

def c1850 : Contract := original1850.toContract.get (by decide)
theorem binding1850 : original1850.toContract = some c1850 := rfl

theorem checked1850 : check 4000 c1850 = true := by decide

def original1851 : RawOriginal := C014.records[59]'(by decide)
theorem original_id1851 : original1851.index = 1851 := by decide

def c1851 : Contract := original1851.toContract.get (by decide)
theorem binding1851 : original1851.toContract = some c1851 := rfl

theorem checked1851 : check 4000 c1851 = true := by decide

def original1852 : RawOriginal := C014.records[60]'(by decide)
theorem original_id1852 : original1852.index = 1852 := by decide

def c1852 : Contract := original1852.toContract.get (by decide)
theorem binding1852 : original1852.toContract = some c1852 := rfl

theorem checked1852 : check 4000 c1852 = true := by decide

def original1853 : RawOriginal := C014.records[61]'(by decide)
theorem original_id1853 : original1853.index = 1853 := by decide

def c1853 : Contract := original1853.toContract.get (by decide)
theorem binding1853 : original1853.toContract = some c1853 := rfl

theorem checked1853 : check 4000 c1853 = true := by decide

def original1854 : RawOriginal := C014.records[62]'(by decide)
theorem original_id1854 : original1854.index = 1854 := by decide

def c1854 : Contract := original1854.toContract.get (by decide)
theorem binding1854 : original1854.toContract = some c1854 := rfl

theorem checked1854 : check 4000 c1854 = true := by decide

def original1855 : RawOriginal := C014.records[63]'(by decide)
theorem original_id1855 : original1855.index = 1855 := by decide

def c1855 : Contract := original1855.toContract.get (by decide)
theorem binding1855 : original1855.toContract = some c1855 := rfl

theorem checked1855 : check 4000 c1855 = true := by decide

def original1856 : RawOriginal := C014.records[64]'(by decide)
theorem original_id1856 : original1856.index = 1856 := by decide

def c1856 : Contract := original1856.toContract.get (by decide)
theorem binding1856 : original1856.toContract = some c1856 := rfl

theorem checked1856 : check 4000 c1856 = true := by decide

def original1857 : RawOriginal := C014.records[65]'(by decide)
theorem original_id1857 : original1857.index = 1857 := by decide

def c1857 : Contract := original1857.toContract.get (by decide)
theorem binding1857 : original1857.toContract = some c1857 := rfl

theorem checked1857 : check 4000 c1857 = true := by decide

def original1858 : RawOriginal := C014.records[66]'(by decide)
theorem original_id1858 : original1858.index = 1858 := by decide

def c1858 : Contract := original1858.toContract.get (by decide)
theorem binding1858 : original1858.toContract = some c1858 := rfl

theorem checked1858 : check 4000 c1858 = true := by decide

def original1859 : RawOriginal := C014.records[67]'(by decide)
theorem original_id1859 : original1859.index = 1859 := by decide

def c1859 : Contract := original1859.toContract.get (by decide)
theorem binding1859 : original1859.toContract = some c1859 := rfl

theorem checked1859 : check 4000 c1859 = true := by decide

def original1860 : RawOriginal := C014.records[68]'(by decide)
theorem original_id1860 : original1860.index = 1860 := by decide

def c1860 : Contract := original1860.toContract.get (by decide)
theorem binding1860 : original1860.toContract = some c1860 := rfl

theorem checked1860 : check 4000 c1860 = true := by decide

def original1861 : RawOriginal := C014.records[69]'(by decide)
theorem original_id1861 : original1861.index = 1861 := by decide

def c1861 : Contract := original1861.toContract.get (by decide)
theorem binding1861 : original1861.toContract = some c1861 := rfl

theorem checked1861 : check 4000 c1861 = true := by decide

def records : List Certified := [
  ⟨1846, c1846, 4000, checked1846⟩,
  ⟨1847, c1847, 4000, checked1847⟩,
  ⟨1848, c1848, 4000, checked1848⟩,
  ⟨1849, c1849, 4000, checked1849⟩,
  ⟨1850, c1850, 4000, checked1850⟩,
  ⟨1851, c1851, 4000, checked1851⟩,
  ⟨1852, c1852, 4000, checked1852⟩,
  ⟨1853, c1853, 4000, checked1853⟩,
  ⟨1854, c1854, 4000, checked1854⟩,
  ⟨1855, c1855, 4000, checked1855⟩,
  ⟨1856, c1856, 4000, checked1856⟩,
  ⟨1857, c1857, 4000, checked1857⟩,
  ⟨1858, c1858, 4000, checked1858⟩,
  ⟨1859, c1859, 4000, checked1859⟩,
  ⟨1860, c1860, 4000, checked1860⟩,
  ⟨1861, c1861, 4000, checked1861⟩]

end PA215.ContractShards.Shard014Part3
