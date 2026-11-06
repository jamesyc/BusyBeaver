import PA215.CertifiedContracts
import PA215.Census.C015
import PA215.Census.C016
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard015Part7
open PA215.Contracts PA215.Census

def original2038 : RawOriginal := C015.records[118]'(by decide)
theorem original_id2038 : original2038.index = 2038 := by decide

def c2038 : Contract := original2038.toContract.get (by decide)
theorem binding2038 : original2038.toContract = some c2038 := rfl

theorem checked2038 : check 4000 c2038 = true := by decide

def original2039 : RawOriginal := C015.records[119]'(by decide)
theorem original_id2039 : original2039.index = 2039 := by decide

def c2039 : Contract := original2039.toContract.get (by decide)
theorem binding2039 : original2039.toContract = some c2039 := rfl

theorem checked2039 : check 4000 c2039 = true := by decide

def original2040 : RawOriginal := C015.records[120]'(by decide)
theorem original_id2040 : original2040.index = 2040 := by decide

def c2040 : Contract := original2040.toContract.get (by decide)
theorem binding2040 : original2040.toContract = some c2040 := rfl

theorem checked2040 : check 4000 c2040 = true := by decide

def original2041 : RawOriginal := C015.records[121]'(by decide)
theorem original_id2041 : original2041.index = 2041 := by decide

def c2041 : Contract := original2041.toContract.get (by decide)
theorem binding2041 : original2041.toContract = some c2041 := rfl

theorem checked2041 : check 4000 c2041 = true := by decide

def original2042 : RawOriginal := C015.records[122]'(by decide)
theorem original_id2042 : original2042.index = 2042 := by decide

def c2042 : Contract := original2042.toContract.get (by decide)
theorem binding2042 : original2042.toContract = some c2042 := rfl

theorem checked2042 : check 4000 c2042 = true := by decide

def original2043 : RawOriginal := C015.records[123]'(by decide)
theorem original_id2043 : original2043.index = 2043 := by decide

def c2043 : Contract := original2043.toContract.get (by decide)
theorem binding2043 : original2043.toContract = some c2043 := rfl

theorem checked2043 : check 4000 c2043 = true := by decide

def original2044 : RawOriginal := C015.records[124]'(by decide)
theorem original_id2044 : original2044.index = 2044 := by decide

def c2044 : Contract := original2044.toContract.get (by decide)
theorem binding2044 : original2044.toContract = some c2044 := rfl

theorem checked2044 : check 4000 c2044 = true := by decide

def original2045 : RawOriginal := C015.records[125]'(by decide)
theorem original_id2045 : original2045.index = 2045 := by decide

def c2045 : Contract := original2045.toContract.get (by decide)
theorem binding2045 : original2045.toContract = some c2045 := rfl

theorem checked2045 : check 4000 c2045 = true := by decide

def original2046 : RawOriginal := C015.records[126]'(by decide)
theorem original_id2046 : original2046.index = 2046 := by decide

def c2046 : Contract := original2046.toContract.get (by decide)
theorem binding2046 : original2046.toContract = some c2046 := rfl

theorem checked2046 : check 4000 c2046 = true := by decide

def original2047 : RawOriginal := C015.records[127]'(by decide)
theorem original_id2047 : original2047.index = 2047 := by decide

def c2047 : Contract := original2047.toContract.get (by decide)
theorem binding2047 : original2047.toContract = some c2047 := rfl

theorem checked2047 : check 4000 c2047 = true := by decide

def original2048 : RawOriginal := C016.records[0]'(by decide)
theorem original_id2048 : original2048.index = 2048 := by decide

def c2048 : Contract := original2048.toContract.get (by decide)
theorem binding2048 : original2048.toContract = some c2048 := rfl

theorem checked2048 : check 4000 c2048 = true := by decide

def original2049 : RawOriginal := C016.records[1]'(by decide)
theorem original_id2049 : original2049.index = 2049 := by decide

def c2049 : Contract := original2049.toContract.get (by decide)
theorem binding2049 : original2049.toContract = some c2049 := rfl

theorem checked2049 : check 4000 c2049 = true := by decide

def original2050 : RawOriginal := C016.records[2]'(by decide)
theorem original_id2050 : original2050.index = 2050 := by decide

def c2050 : Contract := original2050.toContract.get (by decide)
theorem binding2050 : original2050.toContract = some c2050 := rfl

theorem checked2050 : check 4000 c2050 = true := by decide

def original2051 : RawOriginal := C016.records[3]'(by decide)
theorem original_id2051 : original2051.index = 2051 := by decide

def c2051 : Contract := original2051.toContract.get (by decide)
theorem binding2051 : original2051.toContract = some c2051 := rfl

theorem checked2051 : check 4000 c2051 = true := by decide

def original2052 : RawOriginal := C016.records[4]'(by decide)
theorem original_id2052 : original2052.index = 2052 := by decide

def c2052 : Contract := original2052.toContract.get (by decide)
theorem binding2052 : original2052.toContract = some c2052 := rfl

theorem checked2052 : check 4000 c2052 = true := by decide

def original2053 : RawOriginal := C016.records[5]'(by decide)
theorem original_id2053 : original2053.index = 2053 := by decide

def c2053 : Contract := original2053.toContract.get (by decide)
theorem binding2053 : original2053.toContract = some c2053 := rfl

theorem checked2053 : check 4000 c2053 = true := by decide

def records : List Certified := [
  ⟨2038, c2038, 4000, checked2038⟩,
  ⟨2039, c2039, 4000, checked2039⟩,
  ⟨2040, c2040, 4000, checked2040⟩,
  ⟨2041, c2041, 4000, checked2041⟩,
  ⟨2042, c2042, 4000, checked2042⟩,
  ⟨2043, c2043, 4000, checked2043⟩,
  ⟨2044, c2044, 4000, checked2044⟩,
  ⟨2045, c2045, 4000, checked2045⟩,
  ⟨2046, c2046, 4000, checked2046⟩,
  ⟨2047, c2047, 4000, checked2047⟩,
  ⟨2048, c2048, 4000, checked2048⟩,
  ⟨2049, c2049, 4000, checked2049⟩,
  ⟨2050, c2050, 4000, checked2050⟩,
  ⟨2051, c2051, 4000, checked2051⟩,
  ⟨2052, c2052, 4000, checked2052⟩,
  ⟨2053, c2053, 4000, checked2053⟩]

end PA215.ContractShards.Shard015Part7
