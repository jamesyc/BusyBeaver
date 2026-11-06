import PA215.CertifiedContracts
import PA215.Census.C015
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard015Part0
open PA215.Contracts PA215.Census

def original1926 : RawOriginal := C015.records[6]'(by decide)
theorem original_id1926 : original1926.index = 1926 := by decide

def c1926 : Contract := original1926.toContract.get (by decide)
theorem binding1926 : original1926.toContract = some c1926 := rfl

theorem checked1926 : check 4000 c1926 = true := by decide

def original1927 : RawOriginal := C015.records[7]'(by decide)
theorem original_id1927 : original1927.index = 1927 := by decide

def c1927 : Contract := original1927.toContract.get (by decide)
theorem binding1927 : original1927.toContract = some c1927 := rfl

theorem checked1927 : check 4000 c1927 = true := by decide

def original1928 : RawOriginal := C015.records[8]'(by decide)
theorem original_id1928 : original1928.index = 1928 := by decide

def c1928 : Contract := original1928.toContract.get (by decide)
theorem binding1928 : original1928.toContract = some c1928 := rfl

theorem checked1928 : check 4000 c1928 = true := by decide

def original1929 : RawOriginal := C015.records[9]'(by decide)
theorem original_id1929 : original1929.index = 1929 := by decide

def c1929 : Contract := original1929.toContract.get (by decide)
theorem binding1929 : original1929.toContract = some c1929 := rfl

theorem checked1929 : check 4000 c1929 = true := by decide

def original1930 : RawOriginal := C015.records[10]'(by decide)
theorem original_id1930 : original1930.index = 1930 := by decide

def c1930 : Contract := original1930.toContract.get (by decide)
theorem binding1930 : original1930.toContract = some c1930 := rfl

theorem checked1930 : check 4000 c1930 = true := by decide

def original1931 : RawOriginal := C015.records[11]'(by decide)
theorem original_id1931 : original1931.index = 1931 := by decide

def c1931 : Contract := original1931.toContract.get (by decide)
theorem binding1931 : original1931.toContract = some c1931 := rfl

theorem checked1931 : check 4000 c1931 = true := by decide

def original1932 : RawOriginal := C015.records[12]'(by decide)
theorem original_id1932 : original1932.index = 1932 := by decide

def c1932 : Contract := original1932.toContract.get (by decide)
theorem binding1932 : original1932.toContract = some c1932 := rfl

theorem checked1932 : check 4000 c1932 = true := by decide

def original1933 : RawOriginal := C015.records[13]'(by decide)
theorem original_id1933 : original1933.index = 1933 := by decide

def c1933 : Contract := original1933.toContract.get (by decide)
theorem binding1933 : original1933.toContract = some c1933 := rfl

theorem checked1933 : check 4000 c1933 = true := by decide

def original1934 : RawOriginal := C015.records[14]'(by decide)
theorem original_id1934 : original1934.index = 1934 := by decide

def c1934 : Contract := original1934.toContract.get (by decide)
theorem binding1934 : original1934.toContract = some c1934 := rfl

theorem checked1934 : check 4000 c1934 = true := by decide

def original1935 : RawOriginal := C015.records[15]'(by decide)
theorem original_id1935 : original1935.index = 1935 := by decide

def c1935 : Contract := original1935.toContract.get (by decide)
theorem binding1935 : original1935.toContract = some c1935 := rfl

theorem checked1935 : check 4000 c1935 = true := by decide

def original1936 : RawOriginal := C015.records[16]'(by decide)
theorem original_id1936 : original1936.index = 1936 := by decide

def c1936 : Contract := original1936.toContract.get (by decide)
theorem binding1936 : original1936.toContract = some c1936 := rfl

theorem checked1936 : check 4000 c1936 = true := by decide

def original1937 : RawOriginal := C015.records[17]'(by decide)
theorem original_id1937 : original1937.index = 1937 := by decide

def c1937 : Contract := original1937.toContract.get (by decide)
theorem binding1937 : original1937.toContract = some c1937 := rfl

theorem checked1937 : check 4000 c1937 = true := by decide

def original1938 : RawOriginal := C015.records[18]'(by decide)
theorem original_id1938 : original1938.index = 1938 := by decide

def c1938 : Contract := original1938.toContract.get (by decide)
theorem binding1938 : original1938.toContract = some c1938 := rfl

theorem checked1938 : check 4000 c1938 = true := by decide

def original1939 : RawOriginal := C015.records[19]'(by decide)
theorem original_id1939 : original1939.index = 1939 := by decide

def c1939 : Contract := original1939.toContract.get (by decide)
theorem binding1939 : original1939.toContract = some c1939 := rfl

theorem checked1939 : check 4000 c1939 = true := by decide

def original1940 : RawOriginal := C015.records[20]'(by decide)
theorem original_id1940 : original1940.index = 1940 := by decide

def c1940 : Contract := original1940.toContract.get (by decide)
theorem binding1940 : original1940.toContract = some c1940 := rfl

theorem checked1940 : check 4000 c1940 = true := by decide

def original1941 : RawOriginal := C015.records[21]'(by decide)
theorem original_id1941 : original1941.index = 1941 := by decide

def c1941 : Contract := original1941.toContract.get (by decide)
theorem binding1941 : original1941.toContract = some c1941 := rfl

theorem checked1941 : check 4000 c1941 = true := by decide

def records : List Certified := [
  ⟨1926, c1926, 4000, checked1926⟩,
  ⟨1927, c1927, 4000, checked1927⟩,
  ⟨1928, c1928, 4000, checked1928⟩,
  ⟨1929, c1929, 4000, checked1929⟩,
  ⟨1930, c1930, 4000, checked1930⟩,
  ⟨1931, c1931, 4000, checked1931⟩,
  ⟨1932, c1932, 4000, checked1932⟩,
  ⟨1933, c1933, 4000, checked1933⟩,
  ⟨1934, c1934, 4000, checked1934⟩,
  ⟨1935, c1935, 4000, checked1935⟩,
  ⟨1936, c1936, 4000, checked1936⟩,
  ⟨1937, c1937, 4000, checked1937⟩,
  ⟨1938, c1938, 4000, checked1938⟩,
  ⟨1939, c1939, 4000, checked1939⟩,
  ⟨1940, c1940, 4000, checked1940⟩,
  ⟨1941, c1941, 4000, checked1941⟩]

end PA215.ContractShards.Shard015Part0
