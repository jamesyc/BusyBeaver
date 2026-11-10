import PA215.CertifiedContracts
import PA215.Census.C015
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard015Part2
open PA215.Contracts PA215.Census

def original1958 : RawOriginal := C015.records[38]'(by decide)
theorem original_id1958 : original1958.index = 1958 := by decide

def c1958 : Contract := original1958.toContract.get (by decide)
theorem binding1958 : original1958.toContract = some c1958 := rfl

theorem checked1958 : check 4000 c1958 = true := by decide

def original1959 : RawOriginal := C015.records[39]'(by decide)
theorem original_id1959 : original1959.index = 1959 := by decide

def c1959 : Contract := original1959.toContract.get (by decide)
theorem binding1959 : original1959.toContract = some c1959 := rfl

theorem checked1959 : check 4000 c1959 = true := by decide

def original1960 : RawOriginal := C015.records[40]'(by decide)
theorem original_id1960 : original1960.index = 1960 := by decide

def c1960 : Contract := original1960.toContract.get (by decide)
theorem binding1960 : original1960.toContract = some c1960 := rfl

theorem checked1960 : check 4000 c1960 = true := by decide

def original1961 : RawOriginal := C015.records[41]'(by decide)
theorem original_id1961 : original1961.index = 1961 := by decide

def c1961 : Contract := original1961.toContract.get (by decide)
theorem binding1961 : original1961.toContract = some c1961 := rfl

theorem checked1961 : check 4000 c1961 = true := by decide

def original1962 : RawOriginal := C015.records[42]'(by decide)
theorem original_id1962 : original1962.index = 1962 := by decide

def c1962 : Contract := original1962.toContract.get (by decide)
theorem binding1962 : original1962.toContract = some c1962 := rfl

theorem checked1962 : check 4000 c1962 = true := by decide

def original1963 : RawOriginal := C015.records[43]'(by decide)
theorem original_id1963 : original1963.index = 1963 := by decide

def c1963 : Contract := original1963.toContract.get (by decide)
theorem binding1963 : original1963.toContract = some c1963 := rfl

theorem checked1963 : check 4000 c1963 = true := by decide

def original1964 : RawOriginal := C015.records[44]'(by decide)
theorem original_id1964 : original1964.index = 1964 := by decide

def c1964 : Contract := original1964.toContract.get (by decide)
theorem binding1964 : original1964.toContract = some c1964 := rfl

theorem checked1964 : check 4000 c1964 = true := by decide

def original1965 : RawOriginal := C015.records[45]'(by decide)
theorem original_id1965 : original1965.index = 1965 := by decide

def c1965 : Contract := original1965.toContract.get (by decide)
theorem binding1965 : original1965.toContract = some c1965 := rfl

theorem checked1965 : check 4000 c1965 = true := by decide

def original1966 : RawOriginal := C015.records[46]'(by decide)
theorem original_id1966 : original1966.index = 1966 := by decide

def c1966 : Contract := original1966.toContract.get (by decide)
theorem binding1966 : original1966.toContract = some c1966 := rfl

theorem checked1966 : check 4000 c1966 = true := by decide

def original1967 : RawOriginal := C015.records[47]'(by decide)
theorem original_id1967 : original1967.index = 1967 := by decide

def c1967 : Contract := original1967.toContract.get (by decide)
theorem binding1967 : original1967.toContract = some c1967 := rfl

theorem checked1967 : check 4000 c1967 = true := by decide

def original1968 : RawOriginal := C015.records[48]'(by decide)
theorem original_id1968 : original1968.index = 1968 := by decide

def c1968 : Contract := original1968.toContract.get (by decide)
theorem binding1968 : original1968.toContract = some c1968 := rfl

theorem checked1968 : check 4000 c1968 = true := by decide

def original1969 : RawOriginal := C015.records[49]'(by decide)
theorem original_id1969 : original1969.index = 1969 := by decide

def c1969 : Contract := original1969.toContract.get (by decide)
theorem binding1969 : original1969.toContract = some c1969 := rfl

theorem checked1969 : check 4000 c1969 = true := by decide

def original1970 : RawOriginal := C015.records[50]'(by decide)
theorem original_id1970 : original1970.index = 1970 := by decide

def c1970 : Contract := original1970.toContract.get (by decide)
theorem binding1970 : original1970.toContract = some c1970 := rfl

theorem checked1970 : check 4000 c1970 = true := by decide

def original1971 : RawOriginal := C015.records[51]'(by decide)
theorem original_id1971 : original1971.index = 1971 := by decide

def c1971 : Contract := original1971.toContract.get (by decide)
theorem binding1971 : original1971.toContract = some c1971 := rfl

theorem checked1971 : check 4000 c1971 = true := by decide

def original1972 : RawOriginal := C015.records[52]'(by decide)
theorem original_id1972 : original1972.index = 1972 := by decide

def c1972 : Contract := original1972.toContract.get (by decide)
theorem binding1972 : original1972.toContract = some c1972 := rfl

theorem checked1972 : check 4000 c1972 = true := by decide

def original1973 : RawOriginal := C015.records[53]'(by decide)
theorem original_id1973 : original1973.index = 1973 := by decide

def c1973 : Contract := original1973.toContract.get (by decide)
theorem binding1973 : original1973.toContract = some c1973 := rfl

theorem checked1973 : check 4000 c1973 = true := by decide

def records : List Certified := [
  ⟨1958, c1958, 4000, checked1958⟩,
  ⟨1959, c1959, 4000, checked1959⟩,
  ⟨1960, c1960, 4000, checked1960⟩,
  ⟨1961, c1961, 4000, checked1961⟩,
  ⟨1962, c1962, 4000, checked1962⟩,
  ⟨1963, c1963, 4000, checked1963⟩,
  ⟨1964, c1964, 4000, checked1964⟩,
  ⟨1965, c1965, 4000, checked1965⟩,
  ⟨1966, c1966, 4000, checked1966⟩,
  ⟨1967, c1967, 4000, checked1967⟩,
  ⟨1968, c1968, 4000, checked1968⟩,
  ⟨1969, c1969, 4000, checked1969⟩,
  ⟨1970, c1970, 4000, checked1970⟩,
  ⟨1971, c1971, 4000, checked1971⟩,
  ⟨1972, c1972, 4000, checked1972⟩,
  ⟨1973, c1973, 4000, checked1973⟩]

end PA215.ContractShards.Shard015Part2
