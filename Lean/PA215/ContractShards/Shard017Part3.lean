import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C017
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard017Part3
open PA215.Contracts PA215.Census

def original2230 : RawOriginal := C017.records[54]'(by decide)
theorem original_id2230 : original2230.index = 2230 := by decide

def c2230 : Contract := original2230.toContract.get (by decide)
theorem binding2230 : original2230.toContract = some c2230 := rfl

theorem checked2230 : check 4000 c2230 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2231 : RawOriginal := C017.records[55]'(by decide)
theorem original_id2231 : original2231.index = 2231 := by decide

def c2231 : Contract := original2231.toContract.get (by decide)
theorem binding2231 : original2231.toContract = some c2231 := rfl

theorem checked2231 : check 4000 c2231 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2232 : RawOriginal := C017.records[56]'(by decide)
theorem original_id2232 : original2232.index = 2232 := by decide

def c2232 : Contract := original2232.toContract.get (by decide)
theorem binding2232 : original2232.toContract = some c2232 := rfl

theorem checked2232 : check 4000 c2232 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2233 : RawOriginal := C017.records[57]'(by decide)
theorem original_id2233 : original2233.index = 2233 := by decide

def c2233 : Contract := original2233.toContract.get (by decide)
theorem binding2233 : original2233.toContract = some c2233 := rfl

theorem checked2233 : check 4000 c2233 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2234 : RawOriginal := C017.records[58]'(by decide)
theorem original_id2234 : original2234.index = 2234 := by decide

def c2234 : Contract := original2234.toContract.get (by decide)
theorem binding2234 : original2234.toContract = some c2234 := rfl

theorem checked2234 : check 4000 c2234 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2235 : RawOriginal := C017.records[59]'(by decide)
theorem original_id2235 : original2235.index = 2235 := by decide

def c2235 : Contract := original2235.toContract.get (by decide)
theorem binding2235 : original2235.toContract = some c2235 := rfl

theorem checked2235 : check 4000 c2235 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2236 : RawOriginal := C017.records[60]'(by decide)
theorem original_id2236 : original2236.index = 2236 := by decide

def c2236 : Contract := original2236.toContract.get (by decide)
theorem binding2236 : original2236.toContract = some c2236 := rfl

theorem checked2236 : check 4000 c2236 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2237 : RawOriginal := C017.records[61]'(by decide)
theorem original_id2237 : original2237.index = 2237 := by decide

def c2237 : Contract := original2237.toContract.get (by decide)
theorem binding2237 : original2237.toContract = some c2237 := rfl

theorem checked2237 : check 4000 c2237 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2238 : RawOriginal := C017.records[62]'(by decide)
theorem original_id2238 : original2238.index = 2238 := by decide

def c2238 : Contract := original2238.toContract.get (by decide)
theorem binding2238 : original2238.toContract = some c2238 := rfl

theorem checked2238 : check 4000 c2238 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2239 : RawOriginal := C017.records[63]'(by decide)
theorem original_id2239 : original2239.index = 2239 := by decide

def c2239 : Contract := original2239.toContract.get (by decide)
theorem binding2239 : original2239.toContract = some c2239 := rfl

theorem checked2239 : check 4000 c2239 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2240 : RawOriginal := C017.records[64]'(by decide)
theorem original_id2240 : original2240.index = 2240 := by decide

def c2240 : Contract := original2240.toContract.get (by decide)
theorem binding2240 : original2240.toContract = some c2240 := rfl

theorem checked2240 : check 4000 c2240 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2241 : RawOriginal := C017.records[65]'(by decide)
theorem original_id2241 : original2241.index = 2241 := by decide

def c2241 : Contract := original2241.toContract.get (by decide)
theorem binding2241 : original2241.toContract = some c2241 := rfl

theorem checked2241 : check 4000 c2241 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2242 : RawOriginal := C017.records[66]'(by decide)
theorem original_id2242 : original2242.index = 2242 := by decide

def c2242 : Contract := original2242.toContract.get (by decide)
theorem binding2242 : original2242.toContract = some c2242 := rfl

theorem checked2242 : check 4000 c2242 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2243 : RawOriginal := C017.records[67]'(by decide)
theorem original_id2243 : original2243.index = 2243 := by decide

def c2243 : Contract := original2243.toContract.get (by decide)
theorem binding2243 : original2243.toContract = some c2243 := rfl

theorem checked2243 : check 4000 c2243 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2244 : RawOriginal := C017.records[68]'(by decide)
theorem original_id2244 : original2244.index = 2244 := by decide

def c2244 : Contract := original2244.toContract.get (by decide)
theorem binding2244 : original2244.toContract = some c2244 := rfl

theorem checked2244 : check 4000 c2244 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2245 : RawOriginal := C017.records[69]'(by decide)
theorem original_id2245 : original2245.index = 2245 := by decide

def c2245 : Contract := original2245.toContract.get (by decide)
theorem binding2245 : original2245.toContract = some c2245 := rfl

theorem checked2245 : check 4000 c2245 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2230, c2230, 4000, checked2230⟩,
  ⟨2231, c2231, 4000, checked2231⟩,
  ⟨2232, c2232, 4000, checked2232⟩,
  ⟨2233, c2233, 4000, checked2233⟩,
  ⟨2234, c2234, 4000, checked2234⟩,
  ⟨2235, c2235, 4000, checked2235⟩,
  ⟨2236, c2236, 4000, checked2236⟩,
  ⟨2237, c2237, 4000, checked2237⟩,
  ⟨2238, c2238, 4000, checked2238⟩,
  ⟨2239, c2239, 4000, checked2239⟩,
  ⟨2240, c2240, 4000, checked2240⟩,
  ⟨2241, c2241, 4000, checked2241⟩,
  ⟨2242, c2242, 4000, checked2242⟩,
  ⟨2243, c2243, 4000, checked2243⟩,
  ⟨2244, c2244, 4000, checked2244⟩,
  ⟨2245, c2245, 4000, checked2245⟩]

end PA215.ContractShards.Shard017Part3
