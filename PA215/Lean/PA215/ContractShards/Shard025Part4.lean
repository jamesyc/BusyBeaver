import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C025
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard025Part4
open PA215.Contracts PA215.Census

def original3270 : RawOriginal := C025.records[70]'(by decide)
theorem original_id3270 : original3270.index = 3270 := by decide

def c3270 : Contract := original3270.toContract.get (by decide)
theorem binding3270 : original3270.toContract = some c3270 := rfl

theorem checked3270 : check 4000 c3270 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3271 : RawOriginal := C025.records[71]'(by decide)
theorem original_id3271 : original3271.index = 3271 := by decide

def c3271 : Contract := original3271.toContract.get (by decide)
theorem binding3271 : original3271.toContract = some c3271 := rfl

theorem checked3271 : check 4000 c3271 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3272 : RawOriginal := C025.records[72]'(by decide)
theorem original_id3272 : original3272.index = 3272 := by decide

def c3272 : Contract := original3272.toContract.get (by decide)
theorem binding3272 : original3272.toContract = some c3272 := rfl

theorem checked3272 : check 4000 c3272 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3273 : RawOriginal := C025.records[73]'(by decide)
theorem original_id3273 : original3273.index = 3273 := by decide

def c3273 : Contract := original3273.toContract.get (by decide)
theorem binding3273 : original3273.toContract = some c3273 := rfl

theorem checked3273 : check 4000 c3273 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3274 : RawOriginal := C025.records[74]'(by decide)
theorem original_id3274 : original3274.index = 3274 := by decide

def c3274 : Contract := original3274.toContract.get (by decide)
theorem binding3274 : original3274.toContract = some c3274 := rfl

theorem checked3274 : check 4000 c3274 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3275 : RawOriginal := C025.records[75]'(by decide)
theorem original_id3275 : original3275.index = 3275 := by decide

def c3275 : Contract := original3275.toContract.get (by decide)
theorem binding3275 : original3275.toContract = some c3275 := rfl

theorem checked3275 : check 4000 c3275 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3276 : RawOriginal := C025.records[76]'(by decide)
theorem original_id3276 : original3276.index = 3276 := by decide

def c3276 : Contract := original3276.toContract.get (by decide)
theorem binding3276 : original3276.toContract = some c3276 := rfl

theorem checked3276 : check 4000 c3276 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3277 : RawOriginal := C025.records[77]'(by decide)
theorem original_id3277 : original3277.index = 3277 := by decide

def c3277 : Contract := original3277.toContract.get (by decide)
theorem binding3277 : original3277.toContract = some c3277 := rfl

theorem checked3277 : check 4000 c3277 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3278 : RawOriginal := C025.records[78]'(by decide)
theorem original_id3278 : original3278.index = 3278 := by decide

def c3278 : Contract := original3278.toContract.get (by decide)
theorem binding3278 : original3278.toContract = some c3278 := rfl

theorem checked3278 : check 4000 c3278 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3279 : RawOriginal := C025.records[79]'(by decide)
theorem original_id3279 : original3279.index = 3279 := by decide

def c3279 : Contract := original3279.toContract.get (by decide)
theorem binding3279 : original3279.toContract = some c3279 := rfl

theorem checked3279 : check 4000 c3279 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3280 : RawOriginal := C025.records[80]'(by decide)
theorem original_id3280 : original3280.index = 3280 := by decide

def c3280 : Contract := original3280.toContract.get (by decide)
theorem binding3280 : original3280.toContract = some c3280 := rfl

theorem checked3280 : check 4000 c3280 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3281 : RawOriginal := C025.records[81]'(by decide)
theorem original_id3281 : original3281.index = 3281 := by decide

def c3281 : Contract := original3281.toContract.get (by decide)
theorem binding3281 : original3281.toContract = some c3281 := rfl

theorem checked3281 : check 4000 c3281 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3282 : RawOriginal := C025.records[82]'(by decide)
theorem original_id3282 : original3282.index = 3282 := by decide

def c3282 : Contract := original3282.toContract.get (by decide)
theorem binding3282 : original3282.toContract = some c3282 := rfl

theorem checked3282 : check 4000 c3282 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3283 : RawOriginal := C025.records[83]'(by decide)
theorem original_id3283 : original3283.index = 3283 := by decide

def c3283 : Contract := original3283.toContract.get (by decide)
theorem binding3283 : original3283.toContract = some c3283 := rfl

theorem checked3283 : check 4000 c3283 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3284 : RawOriginal := C025.records[84]'(by decide)
theorem original_id3284 : original3284.index = 3284 := by decide

def c3284 : Contract := original3284.toContract.get (by decide)
theorem binding3284 : original3284.toContract = some c3284 := rfl

theorem checked3284 : check 4000 c3284 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3285 : RawOriginal := C025.records[85]'(by decide)
theorem original_id3285 : original3285.index = 3285 := by decide

def c3285 : Contract := original3285.toContract.get (by decide)
theorem binding3285 : original3285.toContract = some c3285 := rfl

theorem checked3285 : check 4000 c3285 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3270, c3270, 4000, checked3270⟩,
  ⟨3271, c3271, 4000, checked3271⟩,
  ⟨3272, c3272, 4000, checked3272⟩,
  ⟨3273, c3273, 4000, checked3273⟩,
  ⟨3274, c3274, 4000, checked3274⟩,
  ⟨3275, c3275, 4000, checked3275⟩,
  ⟨3276, c3276, 4000, checked3276⟩,
  ⟨3277, c3277, 4000, checked3277⟩,
  ⟨3278, c3278, 4000, checked3278⟩,
  ⟨3279, c3279, 4000, checked3279⟩,
  ⟨3280, c3280, 4000, checked3280⟩,
  ⟨3281, c3281, 4000, checked3281⟩,
  ⟨3282, c3282, 4000, checked3282⟩,
  ⟨3283, c3283, 4000, checked3283⟩,
  ⟨3284, c3284, 4000, checked3284⟩,
  ⟨3285, c3285, 4000, checked3285⟩]

end PA215.ContractShards.Shard025Part4
