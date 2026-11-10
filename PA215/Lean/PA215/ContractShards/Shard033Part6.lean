import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C033
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard033Part6
open PA215.Contracts PA215.Census

def original4326 : RawOriginal := C033.records[102]'(by decide)
theorem original_id4326 : original4326.index = 4326 := by decide

def c4326 : Contract := original4326.toContract.get (by decide)
theorem binding4326 : original4326.toContract = some c4326 := rfl

theorem checked4326 : check 4000 c4326 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4327 : RawOriginal := C033.records[103]'(by decide)
theorem original_id4327 : original4327.index = 4327 := by decide

def c4327 : Contract := original4327.toContract.get (by decide)
theorem binding4327 : original4327.toContract = some c4327 := rfl

theorem checked4327 : check 4000 c4327 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4328 : RawOriginal := C033.records[104]'(by decide)
theorem original_id4328 : original4328.index = 4328 := by decide

def c4328 : Contract := original4328.toContract.get (by decide)
theorem binding4328 : original4328.toContract = some c4328 := rfl

theorem checked4328 : check 4000 c4328 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4329 : RawOriginal := C033.records[105]'(by decide)
theorem original_id4329 : original4329.index = 4329 := by decide

def c4329 : Contract := original4329.toContract.get (by decide)
theorem binding4329 : original4329.toContract = some c4329 := rfl

theorem checked4329 : check 4000 c4329 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4330 : RawOriginal := C033.records[106]'(by decide)
theorem original_id4330 : original4330.index = 4330 := by decide

def c4330 : Contract := original4330.toContract.get (by decide)
theorem binding4330 : original4330.toContract = some c4330 := rfl

theorem checked4330 : check 4000 c4330 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4331 : RawOriginal := C033.records[107]'(by decide)
theorem original_id4331 : original4331.index = 4331 := by decide

def c4331 : Contract := original4331.toContract.get (by decide)
theorem binding4331 : original4331.toContract = some c4331 := rfl

theorem checked4331 : check 4000 c4331 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4332 : RawOriginal := C033.records[108]'(by decide)
theorem original_id4332 : original4332.index = 4332 := by decide

def c4332 : Contract := original4332.toContract.get (by decide)
theorem binding4332 : original4332.toContract = some c4332 := rfl

theorem checked4332 : check 4000 c4332 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4333 : RawOriginal := C033.records[109]'(by decide)
theorem original_id4333 : original4333.index = 4333 := by decide

def c4333 : Contract := original4333.toContract.get (by decide)
theorem binding4333 : original4333.toContract = some c4333 := rfl

theorem checked4333 : check 4000 c4333 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4334 : RawOriginal := C033.records[110]'(by decide)
theorem original_id4334 : original4334.index = 4334 := by decide

def c4334 : Contract := original4334.toContract.get (by decide)
theorem binding4334 : original4334.toContract = some c4334 := rfl

theorem checked4334 : check 4000 c4334 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4335 : RawOriginal := C033.records[111]'(by decide)
theorem original_id4335 : original4335.index = 4335 := by decide

def c4335 : Contract := original4335.toContract.get (by decide)
theorem binding4335 : original4335.toContract = some c4335 := rfl

theorem checked4335 : check 4000 c4335 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4336 : RawOriginal := C033.records[112]'(by decide)
theorem original_id4336 : original4336.index = 4336 := by decide

def c4336 : Contract := original4336.toContract.get (by decide)
theorem binding4336 : original4336.toContract = some c4336 := rfl

theorem checked4336 : check 4000 c4336 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4337 : RawOriginal := C033.records[113]'(by decide)
theorem original_id4337 : original4337.index = 4337 := by decide

def c4337 : Contract := original4337.toContract.get (by decide)
theorem binding4337 : original4337.toContract = some c4337 := rfl

theorem checked4337 : check 4000 c4337 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4338 : RawOriginal := C033.records[114]'(by decide)
theorem original_id4338 : original4338.index = 4338 := by decide

def c4338 : Contract := original4338.toContract.get (by decide)
theorem binding4338 : original4338.toContract = some c4338 := rfl

theorem checked4338 : check 4000 c4338 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4339 : RawOriginal := C033.records[115]'(by decide)
theorem original_id4339 : original4339.index = 4339 := by decide

def c4339 : Contract := original4339.toContract.get (by decide)
theorem binding4339 : original4339.toContract = some c4339 := rfl

theorem checked4339 : check 4000 c4339 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4340 : RawOriginal := C033.records[116]'(by decide)
theorem original_id4340 : original4340.index = 4340 := by decide

def c4340 : Contract := original4340.toContract.get (by decide)
theorem binding4340 : original4340.toContract = some c4340 := rfl

theorem checked4340 : check 4000 c4340 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4341 : RawOriginal := C033.records[117]'(by decide)
theorem original_id4341 : original4341.index = 4341 := by decide

def c4341 : Contract := original4341.toContract.get (by decide)
theorem binding4341 : original4341.toContract = some c4341 := rfl

theorem checked4341 : check 4000 c4341 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4326, c4326, 4000, checked4326⟩,
  ⟨4327, c4327, 4000, checked4327⟩,
  ⟨4328, c4328, 4000, checked4328⟩,
  ⟨4329, c4329, 4000, checked4329⟩,
  ⟨4330, c4330, 4000, checked4330⟩,
  ⟨4331, c4331, 4000, checked4331⟩,
  ⟨4332, c4332, 4000, checked4332⟩,
  ⟨4333, c4333, 4000, checked4333⟩,
  ⟨4334, c4334, 4000, checked4334⟩,
  ⟨4335, c4335, 4000, checked4335⟩,
  ⟨4336, c4336, 4000, checked4336⟩,
  ⟨4337, c4337, 4000, checked4337⟩,
  ⟨4338, c4338, 4000, checked4338⟩,
  ⟨4339, c4339, 4000, checked4339⟩,
  ⟨4340, c4340, 4000, checked4340⟩,
  ⟨4341, c4341, 4000, checked4341⟩]

end PA215.ContractShards.Shard033Part6
