import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C017
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard017Part5
open PA215.Contracts PA215.Census

def original2262 : RawOriginal := C017.records[86]'(by decide)
theorem original_id2262 : original2262.index = 2262 := by decide

def c2262 : Contract := original2262.toContract.get (by decide)
theorem binding2262 : original2262.toContract = some c2262 := rfl

theorem checked2262 : check 4000 c2262 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2263 : RawOriginal := C017.records[87]'(by decide)
theorem original_id2263 : original2263.index = 2263 := by decide

def c2263 : Contract := original2263.toContract.get (by decide)
theorem binding2263 : original2263.toContract = some c2263 := rfl

theorem checked2263 : check 4000 c2263 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2264 : RawOriginal := C017.records[88]'(by decide)
theorem original_id2264 : original2264.index = 2264 := by decide

def c2264 : Contract := original2264.toContract.get (by decide)
theorem binding2264 : original2264.toContract = some c2264 := rfl

theorem checked2264 : check 4000 c2264 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2265 : RawOriginal := C017.records[89]'(by decide)
theorem original_id2265 : original2265.index = 2265 := by decide

def c2265 : Contract := original2265.toContract.get (by decide)
theorem binding2265 : original2265.toContract = some c2265 := rfl

theorem checked2265 : check 4000 c2265 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2266 : RawOriginal := C017.records[90]'(by decide)
theorem original_id2266 : original2266.index = 2266 := by decide

def c2266 : Contract := original2266.toContract.get (by decide)
theorem binding2266 : original2266.toContract = some c2266 := rfl

theorem checked2266 : check 4000 c2266 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2267 : RawOriginal := C017.records[91]'(by decide)
theorem original_id2267 : original2267.index = 2267 := by decide

def c2267 : Contract := original2267.toContract.get (by decide)
theorem binding2267 : original2267.toContract = some c2267 := rfl

theorem checked2267 : check 4000 c2267 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2268 : RawOriginal := C017.records[92]'(by decide)
theorem original_id2268 : original2268.index = 2268 := by decide

def c2268 : Contract := original2268.toContract.get (by decide)
theorem binding2268 : original2268.toContract = some c2268 := rfl

theorem checked2268 : check 4000 c2268 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2269 : RawOriginal := C017.records[93]'(by decide)
theorem original_id2269 : original2269.index = 2269 := by decide

def c2269 : Contract := original2269.toContract.get (by decide)
theorem binding2269 : original2269.toContract = some c2269 := rfl

theorem checked2269 : check 4000 c2269 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2270 : RawOriginal := C017.records[94]'(by decide)
theorem original_id2270 : original2270.index = 2270 := by decide

def c2270 : Contract := original2270.toContract.get (by decide)
theorem binding2270 : original2270.toContract = some c2270 := rfl

theorem checked2270 : check 4000 c2270 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2271 : RawOriginal := C017.records[95]'(by decide)
theorem original_id2271 : original2271.index = 2271 := by decide

def c2271 : Contract := original2271.toContract.get (by decide)
theorem binding2271 : original2271.toContract = some c2271 := rfl

theorem checked2271 : check 4000 c2271 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2272 : RawOriginal := C017.records[96]'(by decide)
theorem original_id2272 : original2272.index = 2272 := by decide

def c2272 : Contract := original2272.toContract.get (by decide)
theorem binding2272 : original2272.toContract = some c2272 := rfl

theorem checked2272 : check 4000 c2272 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2273 : RawOriginal := C017.records[97]'(by decide)
theorem original_id2273 : original2273.index = 2273 := by decide

def c2273 : Contract := original2273.toContract.get (by decide)
theorem binding2273 : original2273.toContract = some c2273 := rfl

theorem checked2273 : check 4000 c2273 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2274 : RawOriginal := C017.records[98]'(by decide)
theorem original_id2274 : original2274.index = 2274 := by decide

def c2274 : Contract := original2274.toContract.get (by decide)
theorem binding2274 : original2274.toContract = some c2274 := rfl

theorem checked2274 : check 4000 c2274 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2275 : RawOriginal := C017.records[99]'(by decide)
theorem original_id2275 : original2275.index = 2275 := by decide

def c2275 : Contract := original2275.toContract.get (by decide)
theorem binding2275 : original2275.toContract = some c2275 := rfl

theorem checked2275 : check 4000 c2275 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2276 : RawOriginal := C017.records[100]'(by decide)
theorem original_id2276 : original2276.index = 2276 := by decide

def c2276 : Contract := original2276.toContract.get (by decide)
theorem binding2276 : original2276.toContract = some c2276 := rfl

theorem checked2276 : check 4000 c2276 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2277 : RawOriginal := C017.records[101]'(by decide)
theorem original_id2277 : original2277.index = 2277 := by decide

def c2277 : Contract := original2277.toContract.get (by decide)
theorem binding2277 : original2277.toContract = some c2277 := rfl

theorem checked2277 : check 4000 c2277 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2262, c2262, 4000, checked2262⟩,
  ⟨2263, c2263, 4000, checked2263⟩,
  ⟨2264, c2264, 4000, checked2264⟩,
  ⟨2265, c2265, 4000, checked2265⟩,
  ⟨2266, c2266, 4000, checked2266⟩,
  ⟨2267, c2267, 4000, checked2267⟩,
  ⟨2268, c2268, 4000, checked2268⟩,
  ⟨2269, c2269, 4000, checked2269⟩,
  ⟨2270, c2270, 4000, checked2270⟩,
  ⟨2271, c2271, 4000, checked2271⟩,
  ⟨2272, c2272, 4000, checked2272⟩,
  ⟨2273, c2273, 4000, checked2273⟩,
  ⟨2274, c2274, 4000, checked2274⟩,
  ⟨2275, c2275, 4000, checked2275⟩,
  ⟨2276, c2276, 4000, checked2276⟩,
  ⟨2277, c2277, 4000, checked2277⟩]

end PA215.ContractShards.Shard017Part5
