import PA215.CertifiedContracts
import PA215.Census.C015
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard015Part1
open PA215.Contracts PA215.Census

def original1942 : RawOriginal := C015.records[22]'(by decide)
theorem original_id1942 : original1942.index = 1942 := by decide

def c1942 : Contract := original1942.toContract.get (by decide)
theorem binding1942 : original1942.toContract = some c1942 := rfl

theorem checked1942 : check 4000 c1942 = true := by decide

def original1943 : RawOriginal := C015.records[23]'(by decide)
theorem original_id1943 : original1943.index = 1943 := by decide

def c1943 : Contract := original1943.toContract.get (by decide)
theorem binding1943 : original1943.toContract = some c1943 := rfl

theorem checked1943 : check 4000 c1943 = true := by decide

def original1944 : RawOriginal := C015.records[24]'(by decide)
theorem original_id1944 : original1944.index = 1944 := by decide

def c1944 : Contract := original1944.toContract.get (by decide)
theorem binding1944 : original1944.toContract = some c1944 := rfl

theorem checked1944 : check 4000 c1944 = true := by decide

def original1945 : RawOriginal := C015.records[25]'(by decide)
theorem original_id1945 : original1945.index = 1945 := by decide

def c1945 : Contract := original1945.toContract.get (by decide)
theorem binding1945 : original1945.toContract = some c1945 := rfl

theorem checked1945 : check 4000 c1945 = true := by decide

def original1946 : RawOriginal := C015.records[26]'(by decide)
theorem original_id1946 : original1946.index = 1946 := by decide

def c1946 : Contract := original1946.toContract.get (by decide)
theorem binding1946 : original1946.toContract = some c1946 := rfl

theorem checked1946 : check 4000 c1946 = true := by decide

def original1947 : RawOriginal := C015.records[27]'(by decide)
theorem original_id1947 : original1947.index = 1947 := by decide

def c1947 : Contract := original1947.toContract.get (by decide)
theorem binding1947 : original1947.toContract = some c1947 := rfl

theorem checked1947 : check 4000 c1947 = true := by decide

def original1948 : RawOriginal := C015.records[28]'(by decide)
theorem original_id1948 : original1948.index = 1948 := by decide

def c1948 : Contract := original1948.toContract.get (by decide)
theorem binding1948 : original1948.toContract = some c1948 := rfl

theorem checked1948 : check 4000 c1948 = true := by decide

def original1949 : RawOriginal := C015.records[29]'(by decide)
theorem original_id1949 : original1949.index = 1949 := by decide

def c1949 : Contract := original1949.toContract.get (by decide)
theorem binding1949 : original1949.toContract = some c1949 := rfl

theorem checked1949 : check 4000 c1949 = true := by decide

def original1950 : RawOriginal := C015.records[30]'(by decide)
theorem original_id1950 : original1950.index = 1950 := by decide

def c1950 : Contract := original1950.toContract.get (by decide)
theorem binding1950 : original1950.toContract = some c1950 := rfl

theorem checked1950 : check 4000 c1950 = true := by decide

def original1951 : RawOriginal := C015.records[31]'(by decide)
theorem original_id1951 : original1951.index = 1951 := by decide

def c1951 : Contract := original1951.toContract.get (by decide)
theorem binding1951 : original1951.toContract = some c1951 := rfl

theorem checked1951 : check 4000 c1951 = true := by decide

def original1952 : RawOriginal := C015.records[32]'(by decide)
theorem original_id1952 : original1952.index = 1952 := by decide

def c1952 : Contract := original1952.toContract.get (by decide)
theorem binding1952 : original1952.toContract = some c1952 := rfl

theorem checked1952 : check 4000 c1952 = true := by decide

def original1953 : RawOriginal := C015.records[33]'(by decide)
theorem original_id1953 : original1953.index = 1953 := by decide

def c1953 : Contract := original1953.toContract.get (by decide)
theorem binding1953 : original1953.toContract = some c1953 := rfl

theorem checked1953 : check 4000 c1953 = true := by decide

def original1954 : RawOriginal := C015.records[34]'(by decide)
theorem original_id1954 : original1954.index = 1954 := by decide

def c1954 : Contract := original1954.toContract.get (by decide)
theorem binding1954 : original1954.toContract = some c1954 := rfl

theorem checked1954 : check 4000 c1954 = true := by decide

def original1955 : RawOriginal := C015.records[35]'(by decide)
theorem original_id1955 : original1955.index = 1955 := by decide

def c1955 : Contract := original1955.toContract.get (by decide)
theorem binding1955 : original1955.toContract = some c1955 := rfl

theorem checked1955 : check 4000 c1955 = true := by decide

def original1956 : RawOriginal := C015.records[36]'(by decide)
theorem original_id1956 : original1956.index = 1956 := by decide

def c1956 : Contract := original1956.toContract.get (by decide)
theorem binding1956 : original1956.toContract = some c1956 := rfl

theorem checked1956 : check 4000 c1956 = true := by decide

def original1957 : RawOriginal := C015.records[37]'(by decide)
theorem original_id1957 : original1957.index = 1957 := by decide

def c1957 : Contract := original1957.toContract.get (by decide)
theorem binding1957 : original1957.toContract = some c1957 := rfl

theorem checked1957 : check 4000 c1957 = true := by decide

def records : List Certified := [
  ⟨1942, c1942, 4000, checked1942⟩,
  ⟨1943, c1943, 4000, checked1943⟩,
  ⟨1944, c1944, 4000, checked1944⟩,
  ⟨1945, c1945, 4000, checked1945⟩,
  ⟨1946, c1946, 4000, checked1946⟩,
  ⟨1947, c1947, 4000, checked1947⟩,
  ⟨1948, c1948, 4000, checked1948⟩,
  ⟨1949, c1949, 4000, checked1949⟩,
  ⟨1950, c1950, 4000, checked1950⟩,
  ⟨1951, c1951, 4000, checked1951⟩,
  ⟨1952, c1952, 4000, checked1952⟩,
  ⟨1953, c1953, 4000, checked1953⟩,
  ⟨1954, c1954, 4000, checked1954⟩,
  ⟨1955, c1955, 4000, checked1955⟩,
  ⟨1956, c1956, 4000, checked1956⟩,
  ⟨1957, c1957, 4000, checked1957⟩]

end PA215.ContractShards.Shard015Part1
