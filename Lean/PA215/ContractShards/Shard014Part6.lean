import PA215.CertifiedContracts
import PA215.Census.C014
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard014Part6
open PA215.Contracts PA215.Census

def original1894 : RawOriginal := C014.records[102]'(by decide)
theorem original_id1894 : original1894.index = 1894 := by decide

def c1894 : Contract := original1894.toContract.get (by decide)
theorem binding1894 : original1894.toContract = some c1894 := rfl

theorem checked1894 : check 4000 c1894 = true := by decide

def original1895 : RawOriginal := C014.records[103]'(by decide)
theorem original_id1895 : original1895.index = 1895 := by decide

def c1895 : Contract := original1895.toContract.get (by decide)
theorem binding1895 : original1895.toContract = some c1895 := rfl

theorem checked1895 : check 4000 c1895 = true := by decide

def original1896 : RawOriginal := C014.records[104]'(by decide)
theorem original_id1896 : original1896.index = 1896 := by decide

def c1896 : Contract := original1896.toContract.get (by decide)
theorem binding1896 : original1896.toContract = some c1896 := rfl

theorem checked1896 : check 4000 c1896 = true := by decide

def original1897 : RawOriginal := C014.records[105]'(by decide)
theorem original_id1897 : original1897.index = 1897 := by decide

def c1897 : Contract := original1897.toContract.get (by decide)
theorem binding1897 : original1897.toContract = some c1897 := rfl

theorem checked1897 : check 4000 c1897 = true := by decide

def original1898 : RawOriginal := C014.records[106]'(by decide)
theorem original_id1898 : original1898.index = 1898 := by decide

def c1898 : Contract := original1898.toContract.get (by decide)
theorem binding1898 : original1898.toContract = some c1898 := rfl

theorem checked1898 : check 4000 c1898 = true := by decide

def original1899 : RawOriginal := C014.records[107]'(by decide)
theorem original_id1899 : original1899.index = 1899 := by decide

def c1899 : Contract := original1899.toContract.get (by decide)
theorem binding1899 : original1899.toContract = some c1899 := rfl

theorem checked1899 : check 4000 c1899 = true := by decide

def original1900 : RawOriginal := C014.records[108]'(by decide)
theorem original_id1900 : original1900.index = 1900 := by decide

def c1900 : Contract := original1900.toContract.get (by decide)
theorem binding1900 : original1900.toContract = some c1900 := rfl

theorem checked1900 : check 4000 c1900 = true := by decide

def original1901 : RawOriginal := C014.records[109]'(by decide)
theorem original_id1901 : original1901.index = 1901 := by decide

def c1901 : Contract := original1901.toContract.get (by decide)
theorem binding1901 : original1901.toContract = some c1901 := rfl

theorem checked1901 : check 4000 c1901 = true := by decide

def original1902 : RawOriginal := C014.records[110]'(by decide)
theorem original_id1902 : original1902.index = 1902 := by decide

def c1902 : Contract := original1902.toContract.get (by decide)
theorem binding1902 : original1902.toContract = some c1902 := rfl

theorem checked1902 : check 4000 c1902 = true := by decide

def original1903 : RawOriginal := C014.records[111]'(by decide)
theorem original_id1903 : original1903.index = 1903 := by decide

def c1903 : Contract := original1903.toContract.get (by decide)
theorem binding1903 : original1903.toContract = some c1903 := rfl

theorem checked1903 : check 4000 c1903 = true := by decide

def original1904 : RawOriginal := C014.records[112]'(by decide)
theorem original_id1904 : original1904.index = 1904 := by decide

def c1904 : Contract := original1904.toContract.get (by decide)
theorem binding1904 : original1904.toContract = some c1904 := rfl

theorem checked1904 : check 4000 c1904 = true := by decide

def original1905 : RawOriginal := C014.records[113]'(by decide)
theorem original_id1905 : original1905.index = 1905 := by decide

def c1905 : Contract := original1905.toContract.get (by decide)
theorem binding1905 : original1905.toContract = some c1905 := rfl

theorem checked1905 : check 4000 c1905 = true := by decide

def original1906 : RawOriginal := C014.records[114]'(by decide)
theorem original_id1906 : original1906.index = 1906 := by decide

def c1906 : Contract := original1906.toContract.get (by decide)
theorem binding1906 : original1906.toContract = some c1906 := rfl

theorem checked1906 : check 4000 c1906 = true := by decide

def original1907 : RawOriginal := C014.records[115]'(by decide)
theorem original_id1907 : original1907.index = 1907 := by decide

def c1907 : Contract := original1907.toContract.get (by decide)
theorem binding1907 : original1907.toContract = some c1907 := rfl

theorem checked1907 : check 4000 c1907 = true := by decide

def original1908 : RawOriginal := C014.records[116]'(by decide)
theorem original_id1908 : original1908.index = 1908 := by decide

def c1908 : Contract := original1908.toContract.get (by decide)
theorem binding1908 : original1908.toContract = some c1908 := rfl

theorem checked1908 : check 4000 c1908 = true := by decide

def original1909 : RawOriginal := C014.records[117]'(by decide)
theorem original_id1909 : original1909.index = 1909 := by decide

def c1909 : Contract := original1909.toContract.get (by decide)
theorem binding1909 : original1909.toContract = some c1909 := rfl

theorem checked1909 : check 4000 c1909 = true := by decide

def records : List Certified := [
  ⟨1894, c1894, 4000, checked1894⟩,
  ⟨1895, c1895, 4000, checked1895⟩,
  ⟨1896, c1896, 4000, checked1896⟩,
  ⟨1897, c1897, 4000, checked1897⟩,
  ⟨1898, c1898, 4000, checked1898⟩,
  ⟨1899, c1899, 4000, checked1899⟩,
  ⟨1900, c1900, 4000, checked1900⟩,
  ⟨1901, c1901, 4000, checked1901⟩,
  ⟨1902, c1902, 4000, checked1902⟩,
  ⟨1903, c1903, 4000, checked1903⟩,
  ⟨1904, c1904, 4000, checked1904⟩,
  ⟨1905, c1905, 4000, checked1905⟩,
  ⟨1906, c1906, 4000, checked1906⟩,
  ⟨1907, c1907, 4000, checked1907⟩,
  ⟨1908, c1908, 4000, checked1908⟩,
  ⟨1909, c1909, 4000, checked1909⟩]

end PA215.ContractShards.Shard014Part6
