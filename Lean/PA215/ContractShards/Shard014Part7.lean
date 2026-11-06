import PA215.CertifiedContracts
import PA215.Census.C014
import PA215.Census.C015
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard014Part7
open PA215.Contracts PA215.Census

def original1910 : RawOriginal := C014.records[118]'(by decide)
theorem original_id1910 : original1910.index = 1910 := by decide

def c1910 : Contract := original1910.toContract.get (by decide)
theorem binding1910 : original1910.toContract = some c1910 := rfl

theorem checked1910 : check 4000 c1910 = true := by decide

def original1911 : RawOriginal := C014.records[119]'(by decide)
theorem original_id1911 : original1911.index = 1911 := by decide

def c1911 : Contract := original1911.toContract.get (by decide)
theorem binding1911 : original1911.toContract = some c1911 := rfl

theorem checked1911 : check 4000 c1911 = true := by decide

def original1912 : RawOriginal := C014.records[120]'(by decide)
theorem original_id1912 : original1912.index = 1912 := by decide

def c1912 : Contract := original1912.toContract.get (by decide)
theorem binding1912 : original1912.toContract = some c1912 := rfl

theorem checked1912 : check 4000 c1912 = true := by decide

def original1913 : RawOriginal := C014.records[121]'(by decide)
theorem original_id1913 : original1913.index = 1913 := by decide

def c1913 : Contract := original1913.toContract.get (by decide)
theorem binding1913 : original1913.toContract = some c1913 := rfl

theorem checked1913 : check 4000 c1913 = true := by decide

def original1914 : RawOriginal := C014.records[122]'(by decide)
theorem original_id1914 : original1914.index = 1914 := by decide

def c1914 : Contract := original1914.toContract.get (by decide)
theorem binding1914 : original1914.toContract = some c1914 := rfl

theorem checked1914 : check 4000 c1914 = true := by decide

def original1915 : RawOriginal := C014.records[123]'(by decide)
theorem original_id1915 : original1915.index = 1915 := by decide

def c1915 : Contract := original1915.toContract.get (by decide)
theorem binding1915 : original1915.toContract = some c1915 := rfl

theorem checked1915 : check 4000 c1915 = true := by decide

def original1916 : RawOriginal := C014.records[124]'(by decide)
theorem original_id1916 : original1916.index = 1916 := by decide

def c1916 : Contract := original1916.toContract.get (by decide)
theorem binding1916 : original1916.toContract = some c1916 := rfl

theorem checked1916 : check 4000 c1916 = true := by decide

def original1917 : RawOriginal := C014.records[125]'(by decide)
theorem original_id1917 : original1917.index = 1917 := by decide

def c1917 : Contract := original1917.toContract.get (by decide)
theorem binding1917 : original1917.toContract = some c1917 := rfl

theorem checked1917 : check 4000 c1917 = true := by decide

def original1918 : RawOriginal := C014.records[126]'(by decide)
theorem original_id1918 : original1918.index = 1918 := by decide

def c1918 : Contract := original1918.toContract.get (by decide)
theorem binding1918 : original1918.toContract = some c1918 := rfl

theorem checked1918 : check 4000 c1918 = true := by decide

def original1919 : RawOriginal := C014.records[127]'(by decide)
theorem original_id1919 : original1919.index = 1919 := by decide

def c1919 : Contract := original1919.toContract.get (by decide)
theorem binding1919 : original1919.toContract = some c1919 := rfl

theorem checked1919 : check 4000 c1919 = true := by decide

def original1920 : RawOriginal := C015.records[0]'(by decide)
theorem original_id1920 : original1920.index = 1920 := by decide

def c1920 : Contract := original1920.toContract.get (by decide)
theorem binding1920 : original1920.toContract = some c1920 := rfl

theorem checked1920 : check 4000 c1920 = true := by decide

def original1921 : RawOriginal := C015.records[1]'(by decide)
theorem original_id1921 : original1921.index = 1921 := by decide

def c1921 : Contract := original1921.toContract.get (by decide)
theorem binding1921 : original1921.toContract = some c1921 := rfl

theorem checked1921 : check 4000 c1921 = true := by decide

def original1922 : RawOriginal := C015.records[2]'(by decide)
theorem original_id1922 : original1922.index = 1922 := by decide

def c1922 : Contract := original1922.toContract.get (by decide)
theorem binding1922 : original1922.toContract = some c1922 := rfl

theorem checked1922 : check 4000 c1922 = true := by decide

def original1923 : RawOriginal := C015.records[3]'(by decide)
theorem original_id1923 : original1923.index = 1923 := by decide

def c1923 : Contract := original1923.toContract.get (by decide)
theorem binding1923 : original1923.toContract = some c1923 := rfl

theorem checked1923 : check 4000 c1923 = true := by decide

def original1924 : RawOriginal := C015.records[4]'(by decide)
theorem original_id1924 : original1924.index = 1924 := by decide

def c1924 : Contract := original1924.toContract.get (by decide)
theorem binding1924 : original1924.toContract = some c1924 := rfl

theorem checked1924 : check 4000 c1924 = true := by decide

def original1925 : RawOriginal := C015.records[5]'(by decide)
theorem original_id1925 : original1925.index = 1925 := by decide

def c1925 : Contract := original1925.toContract.get (by decide)
theorem binding1925 : original1925.toContract = some c1925 := rfl

theorem checked1925 : check 4000 c1925 = true := by decide

def records : List Certified := [
  ⟨1910, c1910, 4000, checked1910⟩,
  ⟨1911, c1911, 4000, checked1911⟩,
  ⟨1912, c1912, 4000, checked1912⟩,
  ⟨1913, c1913, 4000, checked1913⟩,
  ⟨1914, c1914, 4000, checked1914⟩,
  ⟨1915, c1915, 4000, checked1915⟩,
  ⟨1916, c1916, 4000, checked1916⟩,
  ⟨1917, c1917, 4000, checked1917⟩,
  ⟨1918, c1918, 4000, checked1918⟩,
  ⟨1919, c1919, 4000, checked1919⟩,
  ⟨1920, c1920, 4000, checked1920⟩,
  ⟨1921, c1921, 4000, checked1921⟩,
  ⟨1922, c1922, 4000, checked1922⟩,
  ⟨1923, c1923, 4000, checked1923⟩,
  ⟨1924, c1924, 4000, checked1924⟩,
  ⟨1925, c1925, 4000, checked1925⟩]

end PA215.ContractShards.Shard014Part7
