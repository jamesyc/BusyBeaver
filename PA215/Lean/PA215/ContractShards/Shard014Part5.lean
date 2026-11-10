import PA215.CertifiedContracts
import PA215.Census.C014
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard014Part5
open PA215.Contracts PA215.Census

def original1878 : RawOriginal := C014.records[86]'(by decide)
theorem original_id1878 : original1878.index = 1878 := by decide

def c1878 : Contract := original1878.toContract.get (by decide)
theorem binding1878 : original1878.toContract = some c1878 := rfl

theorem checked1878 : check 4000 c1878 = true := by decide

def original1879 : RawOriginal := C014.records[87]'(by decide)
theorem original_id1879 : original1879.index = 1879 := by decide

def c1879 : Contract := original1879.toContract.get (by decide)
theorem binding1879 : original1879.toContract = some c1879 := rfl

theorem checked1879 : check 4000 c1879 = true := by decide

def original1880 : RawOriginal := C014.records[88]'(by decide)
theorem original_id1880 : original1880.index = 1880 := by decide

def c1880 : Contract := original1880.toContract.get (by decide)
theorem binding1880 : original1880.toContract = some c1880 := rfl

theorem checked1880 : check 4000 c1880 = true := by decide

def original1881 : RawOriginal := C014.records[89]'(by decide)
theorem original_id1881 : original1881.index = 1881 := by decide

def c1881 : Contract := original1881.toContract.get (by decide)
theorem binding1881 : original1881.toContract = some c1881 := rfl

theorem checked1881 : check 4000 c1881 = true := by decide

def original1882 : RawOriginal := C014.records[90]'(by decide)
theorem original_id1882 : original1882.index = 1882 := by decide

def c1882 : Contract := original1882.toContract.get (by decide)
theorem binding1882 : original1882.toContract = some c1882 := rfl

theorem checked1882 : check 4000 c1882 = true := by decide

def original1883 : RawOriginal := C014.records[91]'(by decide)
theorem original_id1883 : original1883.index = 1883 := by decide

def c1883 : Contract := original1883.toContract.get (by decide)
theorem binding1883 : original1883.toContract = some c1883 := rfl

theorem checked1883 : check 4000 c1883 = true := by decide

def original1884 : RawOriginal := C014.records[92]'(by decide)
theorem original_id1884 : original1884.index = 1884 := by decide

def c1884 : Contract := original1884.toContract.get (by decide)
theorem binding1884 : original1884.toContract = some c1884 := rfl

theorem checked1884 : check 4000 c1884 = true := by decide

def original1885 : RawOriginal := C014.records[93]'(by decide)
theorem original_id1885 : original1885.index = 1885 := by decide

def c1885 : Contract := original1885.toContract.get (by decide)
theorem binding1885 : original1885.toContract = some c1885 := rfl

theorem checked1885 : check 4000 c1885 = true := by decide

def original1886 : RawOriginal := C014.records[94]'(by decide)
theorem original_id1886 : original1886.index = 1886 := by decide

def c1886 : Contract := original1886.toContract.get (by decide)
theorem binding1886 : original1886.toContract = some c1886 := rfl

theorem checked1886 : check 4000 c1886 = true := by decide

def original1887 : RawOriginal := C014.records[95]'(by decide)
theorem original_id1887 : original1887.index = 1887 := by decide

def c1887 : Contract := original1887.toContract.get (by decide)
theorem binding1887 : original1887.toContract = some c1887 := rfl

theorem checked1887 : check 4000 c1887 = true := by decide

def original1888 : RawOriginal := C014.records[96]'(by decide)
theorem original_id1888 : original1888.index = 1888 := by decide

def c1888 : Contract := original1888.toContract.get (by decide)
theorem binding1888 : original1888.toContract = some c1888 := rfl

theorem checked1888 : check 4000 c1888 = true := by decide

def original1889 : RawOriginal := C014.records[97]'(by decide)
theorem original_id1889 : original1889.index = 1889 := by decide

def c1889 : Contract := original1889.toContract.get (by decide)
theorem binding1889 : original1889.toContract = some c1889 := rfl

theorem checked1889 : check 4000 c1889 = true := by decide

def original1890 : RawOriginal := C014.records[98]'(by decide)
theorem original_id1890 : original1890.index = 1890 := by decide

def c1890 : Contract := original1890.toContract.get (by decide)
theorem binding1890 : original1890.toContract = some c1890 := rfl

theorem checked1890 : check 4000 c1890 = true := by decide

def original1891 : RawOriginal := C014.records[99]'(by decide)
theorem original_id1891 : original1891.index = 1891 := by decide

def c1891 : Contract := original1891.toContract.get (by decide)
theorem binding1891 : original1891.toContract = some c1891 := rfl

theorem checked1891 : check 4000 c1891 = true := by decide

def original1892 : RawOriginal := C014.records[100]'(by decide)
theorem original_id1892 : original1892.index = 1892 := by decide

def c1892 : Contract := original1892.toContract.get (by decide)
theorem binding1892 : original1892.toContract = some c1892 := rfl

theorem checked1892 : check 4000 c1892 = true := by decide

def original1893 : RawOriginal := C014.records[101]'(by decide)
theorem original_id1893 : original1893.index = 1893 := by decide

def c1893 : Contract := original1893.toContract.get (by decide)
theorem binding1893 : original1893.toContract = some c1893 := rfl

theorem checked1893 : check 4000 c1893 = true := by decide

def records : List Certified := [
  ⟨1878, c1878, 4000, checked1878⟩,
  ⟨1879, c1879, 4000, checked1879⟩,
  ⟨1880, c1880, 4000, checked1880⟩,
  ⟨1881, c1881, 4000, checked1881⟩,
  ⟨1882, c1882, 4000, checked1882⟩,
  ⟨1883, c1883, 4000, checked1883⟩,
  ⟨1884, c1884, 4000, checked1884⟩,
  ⟨1885, c1885, 4000, checked1885⟩,
  ⟨1886, c1886, 4000, checked1886⟩,
  ⟨1887, c1887, 4000, checked1887⟩,
  ⟨1888, c1888, 4000, checked1888⟩,
  ⟨1889, c1889, 4000, checked1889⟩,
  ⟨1890, c1890, 4000, checked1890⟩,
  ⟨1891, c1891, 4000, checked1891⟩,
  ⟨1892, c1892, 4000, checked1892⟩,
  ⟨1893, c1893, 4000, checked1893⟩]

end PA215.ContractShards.Shard014Part5
