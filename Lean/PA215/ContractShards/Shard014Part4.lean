import PA215.CertifiedContracts
import PA215.Census.C014
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard014Part4
open PA215.Contracts PA215.Census

def original1862 : RawOriginal := C014.records[70]'(by decide)
theorem original_id1862 : original1862.index = 1862 := by decide

def c1862 : Contract := original1862.toContract.get (by decide)
theorem binding1862 : original1862.toContract = some c1862 := rfl

theorem checked1862 : check 4000 c1862 = true := by decide

def original1863 : RawOriginal := C014.records[71]'(by decide)
theorem original_id1863 : original1863.index = 1863 := by decide

def c1863 : Contract := original1863.toContract.get (by decide)
theorem binding1863 : original1863.toContract = some c1863 := rfl

theorem checked1863 : check 4000 c1863 = true := by decide

def original1864 : RawOriginal := C014.records[72]'(by decide)
theorem original_id1864 : original1864.index = 1864 := by decide

def c1864 : Contract := original1864.toContract.get (by decide)
theorem binding1864 : original1864.toContract = some c1864 := rfl

theorem checked1864 : check 4000 c1864 = true := by decide

def original1865 : RawOriginal := C014.records[73]'(by decide)
theorem original_id1865 : original1865.index = 1865 := by decide

def c1865 : Contract := original1865.toContract.get (by decide)
theorem binding1865 : original1865.toContract = some c1865 := rfl

theorem checked1865 : check 4000 c1865 = true := by decide

def original1866 : RawOriginal := C014.records[74]'(by decide)
theorem original_id1866 : original1866.index = 1866 := by decide

def c1866 : Contract := original1866.toContract.get (by decide)
theorem binding1866 : original1866.toContract = some c1866 := rfl

theorem checked1866 : check 4000 c1866 = true := by decide

def original1867 : RawOriginal := C014.records[75]'(by decide)
theorem original_id1867 : original1867.index = 1867 := by decide

def c1867 : Contract := original1867.toContract.get (by decide)
theorem binding1867 : original1867.toContract = some c1867 := rfl

theorem checked1867 : check 4000 c1867 = true := by decide

def original1868 : RawOriginal := C014.records[76]'(by decide)
theorem original_id1868 : original1868.index = 1868 := by decide

def c1868 : Contract := original1868.toContract.get (by decide)
theorem binding1868 : original1868.toContract = some c1868 := rfl

theorem checked1868 : check 4000 c1868 = true := by decide

def original1869 : RawOriginal := C014.records[77]'(by decide)
theorem original_id1869 : original1869.index = 1869 := by decide

def c1869 : Contract := original1869.toContract.get (by decide)
theorem binding1869 : original1869.toContract = some c1869 := rfl

theorem checked1869 : check 4000 c1869 = true := by decide

def original1870 : RawOriginal := C014.records[78]'(by decide)
theorem original_id1870 : original1870.index = 1870 := by decide

def c1870 : Contract := original1870.toContract.get (by decide)
theorem binding1870 : original1870.toContract = some c1870 := rfl

theorem checked1870 : check 4000 c1870 = true := by decide

def original1871 : RawOriginal := C014.records[79]'(by decide)
theorem original_id1871 : original1871.index = 1871 := by decide

def c1871 : Contract := original1871.toContract.get (by decide)
theorem binding1871 : original1871.toContract = some c1871 := rfl

theorem checked1871 : check 4000 c1871 = true := by decide

def original1872 : RawOriginal := C014.records[80]'(by decide)
theorem original_id1872 : original1872.index = 1872 := by decide

def c1872 : Contract := original1872.toContract.get (by decide)
theorem binding1872 : original1872.toContract = some c1872 := rfl

theorem checked1872 : check 4000 c1872 = true := by decide

def original1873 : RawOriginal := C014.records[81]'(by decide)
theorem original_id1873 : original1873.index = 1873 := by decide

def c1873 : Contract := original1873.toContract.get (by decide)
theorem binding1873 : original1873.toContract = some c1873 := rfl

theorem checked1873 : check 4000 c1873 = true := by decide

def original1874 : RawOriginal := C014.records[82]'(by decide)
theorem original_id1874 : original1874.index = 1874 := by decide

def c1874 : Contract := original1874.toContract.get (by decide)
theorem binding1874 : original1874.toContract = some c1874 := rfl

theorem checked1874 : check 4000 c1874 = true := by decide

def original1875 : RawOriginal := C014.records[83]'(by decide)
theorem original_id1875 : original1875.index = 1875 := by decide

def c1875 : Contract := original1875.toContract.get (by decide)
theorem binding1875 : original1875.toContract = some c1875 := rfl

theorem checked1875 : check 4000 c1875 = true := by decide

def original1876 : RawOriginal := C014.records[84]'(by decide)
theorem original_id1876 : original1876.index = 1876 := by decide

def c1876 : Contract := original1876.toContract.get (by decide)
theorem binding1876 : original1876.toContract = some c1876 := rfl

theorem checked1876 : check 4000 c1876 = true := by decide

def original1877 : RawOriginal := C014.records[85]'(by decide)
theorem original_id1877 : original1877.index = 1877 := by decide

def c1877 : Contract := original1877.toContract.get (by decide)
theorem binding1877 : original1877.toContract = some c1877 := rfl

theorem checked1877 : check 4000 c1877 = true := by decide

def records : List Certified := [
  ⟨1862, c1862, 4000, checked1862⟩,
  ⟨1863, c1863, 4000, checked1863⟩,
  ⟨1864, c1864, 4000, checked1864⟩,
  ⟨1865, c1865, 4000, checked1865⟩,
  ⟨1866, c1866, 4000, checked1866⟩,
  ⟨1867, c1867, 4000, checked1867⟩,
  ⟨1868, c1868, 4000, checked1868⟩,
  ⟨1869, c1869, 4000, checked1869⟩,
  ⟨1870, c1870, 4000, checked1870⟩,
  ⟨1871, c1871, 4000, checked1871⟩,
  ⟨1872, c1872, 4000, checked1872⟩,
  ⟨1873, c1873, 4000, checked1873⟩,
  ⟨1874, c1874, 4000, checked1874⟩,
  ⟨1875, c1875, 4000, checked1875⟩,
  ⟨1876, c1876, 4000, checked1876⟩,
  ⟨1877, c1877, 4000, checked1877⟩]

end PA215.ContractShards.Shard014Part4
