import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C025
import PA215.Census.C026
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard025Part7
open PA215.Contracts PA215.Census

def original3318 : RawOriginal := C025.records[118]'(by decide)
theorem original_id3318 : original3318.index = 3318 := by decide

def c3318 : Contract := original3318.toContract.get (by decide)
theorem binding3318 : original3318.toContract = some c3318 := rfl

theorem checked3318 : check 4000 c3318 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3319 : RawOriginal := C025.records[119]'(by decide)
theorem original_id3319 : original3319.index = 3319 := by decide

def c3319 : Contract := original3319.toContract.get (by decide)
theorem binding3319 : original3319.toContract = some c3319 := rfl

theorem checked3319 : check 4000 c3319 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3320 : RawOriginal := C025.records[120]'(by decide)
theorem original_id3320 : original3320.index = 3320 := by decide

def c3320 : Contract := original3320.toContract.get (by decide)
theorem binding3320 : original3320.toContract = some c3320 := rfl

theorem checked3320 : check 4000 c3320 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3321 : RawOriginal := C025.records[121]'(by decide)
theorem original_id3321 : original3321.index = 3321 := by decide

def c3321 : Contract := original3321.toContract.get (by decide)
theorem binding3321 : original3321.toContract = some c3321 := rfl

theorem checked3321 : check 4000 c3321 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3322 : RawOriginal := C025.records[122]'(by decide)
theorem original_id3322 : original3322.index = 3322 := by decide

def c3322 : Contract := original3322.toContract.get (by decide)
theorem binding3322 : original3322.toContract = some c3322 := rfl

theorem checked3322 : check 4000 c3322 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3323 : RawOriginal := C025.records[123]'(by decide)
theorem original_id3323 : original3323.index = 3323 := by decide

def c3323 : Contract := original3323.toContract.get (by decide)
theorem binding3323 : original3323.toContract = some c3323 := rfl

theorem checked3323 : check 4000 c3323 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3324 : RawOriginal := C025.records[124]'(by decide)
theorem original_id3324 : original3324.index = 3324 := by decide

def c3324 : Contract := original3324.toContract.get (by decide)
theorem binding3324 : original3324.toContract = some c3324 := rfl

theorem checked3324 : check 4000 c3324 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3325 : RawOriginal := C025.records[125]'(by decide)
theorem original_id3325 : original3325.index = 3325 := by decide

def c3325 : Contract := original3325.toContract.get (by decide)
theorem binding3325 : original3325.toContract = some c3325 := rfl

theorem checked3325 : check 4000 c3325 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3326 : RawOriginal := C025.records[126]'(by decide)
theorem original_id3326 : original3326.index = 3326 := by decide

def c3326 : Contract := original3326.toContract.get (by decide)
theorem binding3326 : original3326.toContract = some c3326 := rfl

theorem checked3326 : check 4000 c3326 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3327 : RawOriginal := C025.records[127]'(by decide)
theorem original_id3327 : original3327.index = 3327 := by decide

def c3327 : Contract := original3327.toContract.get (by decide)
theorem binding3327 : original3327.toContract = some c3327 := rfl

theorem checked3327 : check 4000 c3327 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3328 : RawOriginal := C026.records[0]'(by decide)
theorem original_id3328 : original3328.index = 3328 := by decide

def c3328 : Contract := original3328.toContract.get (by decide)
theorem binding3328 : original3328.toContract = some c3328 := rfl

theorem checked3328 : check 4000 c3328 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3329 : RawOriginal := C026.records[1]'(by decide)
theorem original_id3329 : original3329.index = 3329 := by decide

def c3329 : Contract := original3329.toContract.get (by decide)
theorem binding3329 : original3329.toContract = some c3329 := rfl

theorem checked3329 : check 4000 c3329 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3330 : RawOriginal := C026.records[2]'(by decide)
theorem original_id3330 : original3330.index = 3330 := by decide

def c3330 : Contract := original3330.toContract.get (by decide)
theorem binding3330 : original3330.toContract = some c3330 := rfl

theorem checked3330 : check 4000 c3330 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3331 : RawOriginal := C026.records[3]'(by decide)
theorem original_id3331 : original3331.index = 3331 := by decide

def c3331 : Contract := original3331.toContract.get (by decide)
theorem binding3331 : original3331.toContract = some c3331 := rfl

theorem checked3331 : check 4000 c3331 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3332 : RawOriginal := C026.records[4]'(by decide)
theorem original_id3332 : original3332.index = 3332 := by decide

def c3332 : Contract := original3332.toContract.get (by decide)
theorem binding3332 : original3332.toContract = some c3332 := rfl

theorem checked3332 : check 4000 c3332 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3333 : RawOriginal := C026.records[5]'(by decide)
theorem original_id3333 : original3333.index = 3333 := by decide

def c3333 : Contract := original3333.toContract.get (by decide)
theorem binding3333 : original3333.toContract = some c3333 := rfl

theorem checked3333 : check 4000 c3333 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3318, c3318, 4000, checked3318⟩,
  ⟨3319, c3319, 4000, checked3319⟩,
  ⟨3320, c3320, 4000, checked3320⟩,
  ⟨3321, c3321, 4000, checked3321⟩,
  ⟨3322, c3322, 4000, checked3322⟩,
  ⟨3323, c3323, 4000, checked3323⟩,
  ⟨3324, c3324, 4000, checked3324⟩,
  ⟨3325, c3325, 4000, checked3325⟩,
  ⟨3326, c3326, 4000, checked3326⟩,
  ⟨3327, c3327, 4000, checked3327⟩,
  ⟨3328, c3328, 4000, checked3328⟩,
  ⟨3329, c3329, 4000, checked3329⟩,
  ⟨3330, c3330, 4000, checked3330⟩,
  ⟨3331, c3331, 4000, checked3331⟩,
  ⟨3332, c3332, 4000, checked3332⟩,
  ⟨3333, c3333, 4000, checked3333⟩]

end PA215.ContractShards.Shard025Part7
