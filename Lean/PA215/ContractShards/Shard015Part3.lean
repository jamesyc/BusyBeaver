import PA215.CertifiedContracts
import PA215.Census.C015
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard015Part3
open PA215.Contracts PA215.Census

def original1974 : RawOriginal := C015.records[54]'(by decide)
theorem original_id1974 : original1974.index = 1974 := by decide

def c1974 : Contract := original1974.toContract.get (by decide)
theorem binding1974 : original1974.toContract = some c1974 := rfl

theorem checked1974 : check 4000 c1974 = true := by decide

def original1975 : RawOriginal := C015.records[55]'(by decide)
theorem original_id1975 : original1975.index = 1975 := by decide

def c1975 : Contract := original1975.toContract.get (by decide)
theorem binding1975 : original1975.toContract = some c1975 := rfl

theorem checked1975 : check 4000 c1975 = true := by decide

def original1976 : RawOriginal := C015.records[56]'(by decide)
theorem original_id1976 : original1976.index = 1976 := by decide

def c1976 : Contract := original1976.toContract.get (by decide)
theorem binding1976 : original1976.toContract = some c1976 := rfl

theorem checked1976 : check 4000 c1976 = true := by decide

def original1977 : RawOriginal := C015.records[57]'(by decide)
theorem original_id1977 : original1977.index = 1977 := by decide

def c1977 : Contract := original1977.toContract.get (by decide)
theorem binding1977 : original1977.toContract = some c1977 := rfl

theorem checked1977 : check 4000 c1977 = true := by decide

def original1978 : RawOriginal := C015.records[58]'(by decide)
theorem original_id1978 : original1978.index = 1978 := by decide

def c1978 : Contract := original1978.toContract.get (by decide)
theorem binding1978 : original1978.toContract = some c1978 := rfl

theorem checked1978 : check 4000 c1978 = true := by decide

def original1979 : RawOriginal := C015.records[59]'(by decide)
theorem original_id1979 : original1979.index = 1979 := by decide

def c1979 : Contract := original1979.toContract.get (by decide)
theorem binding1979 : original1979.toContract = some c1979 := rfl

theorem checked1979 : check 4000 c1979 = true := by decide

def original1980 : RawOriginal := C015.records[60]'(by decide)
theorem original_id1980 : original1980.index = 1980 := by decide

def c1980 : Contract := original1980.toContract.get (by decide)
theorem binding1980 : original1980.toContract = some c1980 := rfl

theorem checked1980 : check 4000 c1980 = true := by decide

def original1981 : RawOriginal := C015.records[61]'(by decide)
theorem original_id1981 : original1981.index = 1981 := by decide

def c1981 : Contract := original1981.toContract.get (by decide)
theorem binding1981 : original1981.toContract = some c1981 := rfl

theorem checked1981 : check 4000 c1981 = true := by decide

def original1982 : RawOriginal := C015.records[62]'(by decide)
theorem original_id1982 : original1982.index = 1982 := by decide

def c1982 : Contract := original1982.toContract.get (by decide)
theorem binding1982 : original1982.toContract = some c1982 := rfl

theorem checked1982 : check 4000 c1982 = true := by decide

def original1983 : RawOriginal := C015.records[63]'(by decide)
theorem original_id1983 : original1983.index = 1983 := by decide

def c1983 : Contract := original1983.toContract.get (by decide)
theorem binding1983 : original1983.toContract = some c1983 := rfl

theorem checked1983 : check 4000 c1983 = true := by decide

def original1984 : RawOriginal := C015.records[64]'(by decide)
theorem original_id1984 : original1984.index = 1984 := by decide

def c1984 : Contract := original1984.toContract.get (by decide)
theorem binding1984 : original1984.toContract = some c1984 := rfl

theorem checked1984 : check 4000 c1984 = true := by decide

def original1985 : RawOriginal := C015.records[65]'(by decide)
theorem original_id1985 : original1985.index = 1985 := by decide

def c1985 : Contract := original1985.toContract.get (by decide)
theorem binding1985 : original1985.toContract = some c1985 := rfl

theorem checked1985 : check 4000 c1985 = true := by decide

def original1986 : RawOriginal := C015.records[66]'(by decide)
theorem original_id1986 : original1986.index = 1986 := by decide

def c1986 : Contract := original1986.toContract.get (by decide)
theorem binding1986 : original1986.toContract = some c1986 := rfl

theorem checked1986 : check 4000 c1986 = true := by decide

def original1987 : RawOriginal := C015.records[67]'(by decide)
theorem original_id1987 : original1987.index = 1987 := by decide

def c1987 : Contract := original1987.toContract.get (by decide)
theorem binding1987 : original1987.toContract = some c1987 := rfl

theorem checked1987 : check 4000 c1987 = true := by decide

def original1988 : RawOriginal := C015.records[68]'(by decide)
theorem original_id1988 : original1988.index = 1988 := by decide

def c1988 : Contract := original1988.toContract.get (by decide)
theorem binding1988 : original1988.toContract = some c1988 := rfl

theorem checked1988 : check 4000 c1988 = true := by decide

def original1989 : RawOriginal := C015.records[69]'(by decide)
theorem original_id1989 : original1989.index = 1989 := by decide

def c1989 : Contract := original1989.toContract.get (by decide)
theorem binding1989 : original1989.toContract = some c1989 := rfl

theorem checked1989 : check 4000 c1989 = true := by decide

def records : List Certified := [
  ⟨1974, c1974, 4000, checked1974⟩,
  ⟨1975, c1975, 4000, checked1975⟩,
  ⟨1976, c1976, 4000, checked1976⟩,
  ⟨1977, c1977, 4000, checked1977⟩,
  ⟨1978, c1978, 4000, checked1978⟩,
  ⟨1979, c1979, 4000, checked1979⟩,
  ⟨1980, c1980, 4000, checked1980⟩,
  ⟨1981, c1981, 4000, checked1981⟩,
  ⟨1982, c1982, 4000, checked1982⟩,
  ⟨1983, c1983, 4000, checked1983⟩,
  ⟨1984, c1984, 4000, checked1984⟩,
  ⟨1985, c1985, 4000, checked1985⟩,
  ⟨1986, c1986, 4000, checked1986⟩,
  ⟨1987, c1987, 4000, checked1987⟩,
  ⟨1988, c1988, 4000, checked1988⟩,
  ⟨1989, c1989, 4000, checked1989⟩]

end PA215.ContractShards.Shard015Part3
