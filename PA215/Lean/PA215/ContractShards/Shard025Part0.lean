import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C025
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard025Part0
open PA215.Contracts PA215.Census

def original3206 : RawOriginal := C025.records[6]'(by decide)
theorem original_id3206 : original3206.index = 3206 := by decide

def c3206 : Contract := original3206.toContract.get (by decide)
theorem binding3206 : original3206.toContract = some c3206 := rfl

theorem checked3206 : check 4000 c3206 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3207 : RawOriginal := C025.records[7]'(by decide)
theorem original_id3207 : original3207.index = 3207 := by decide

def c3207 : Contract := original3207.toContract.get (by decide)
theorem binding3207 : original3207.toContract = some c3207 := rfl

theorem checked3207 : check 4000 c3207 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3208 : RawOriginal := C025.records[8]'(by decide)
theorem original_id3208 : original3208.index = 3208 := by decide

def c3208 : Contract := original3208.toContract.get (by decide)
theorem binding3208 : original3208.toContract = some c3208 := rfl

theorem checked3208 : check 4000 c3208 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3209 : RawOriginal := C025.records[9]'(by decide)
theorem original_id3209 : original3209.index = 3209 := by decide

def c3209 : Contract := original3209.toContract.get (by decide)
theorem binding3209 : original3209.toContract = some c3209 := rfl

theorem checked3209 : check 4000 c3209 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3210 : RawOriginal := C025.records[10]'(by decide)
theorem original_id3210 : original3210.index = 3210 := by decide

def c3210 : Contract := original3210.toContract.get (by decide)
theorem binding3210 : original3210.toContract = some c3210 := rfl

theorem checked3210 : check 4000 c3210 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3211 : RawOriginal := C025.records[11]'(by decide)
theorem original_id3211 : original3211.index = 3211 := by decide

def c3211 : Contract := original3211.toContract.get (by decide)
theorem binding3211 : original3211.toContract = some c3211 := rfl

theorem checked3211 : check 4000 c3211 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3212 : RawOriginal := C025.records[12]'(by decide)
theorem original_id3212 : original3212.index = 3212 := by decide

def c3212 : Contract := original3212.toContract.get (by decide)
theorem binding3212 : original3212.toContract = some c3212 := rfl

theorem checked3212 : check 4000 c3212 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3213 : RawOriginal := C025.records[13]'(by decide)
theorem original_id3213 : original3213.index = 3213 := by decide

def c3213 : Contract := original3213.toContract.get (by decide)
theorem binding3213 : original3213.toContract = some c3213 := rfl

theorem checked3213 : check 4000 c3213 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3214 : RawOriginal := C025.records[14]'(by decide)
theorem original_id3214 : original3214.index = 3214 := by decide

def c3214 : Contract := original3214.toContract.get (by decide)
theorem binding3214 : original3214.toContract = some c3214 := rfl

theorem checked3214 : check 4000 c3214 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3215 : RawOriginal := C025.records[15]'(by decide)
theorem original_id3215 : original3215.index = 3215 := by decide

def c3215 : Contract := original3215.toContract.get (by decide)
theorem binding3215 : original3215.toContract = some c3215 := rfl

theorem checked3215 : check 4000 c3215 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3216 : RawOriginal := C025.records[16]'(by decide)
theorem original_id3216 : original3216.index = 3216 := by decide

def c3216 : Contract := original3216.toContract.get (by decide)
theorem binding3216 : original3216.toContract = some c3216 := rfl

theorem checked3216 : check 4000 c3216 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3217 : RawOriginal := C025.records[17]'(by decide)
theorem original_id3217 : original3217.index = 3217 := by decide

def c3217 : Contract := original3217.toContract.get (by decide)
theorem binding3217 : original3217.toContract = some c3217 := rfl

theorem checked3217 : check 4000 c3217 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3218 : RawOriginal := C025.records[18]'(by decide)
theorem original_id3218 : original3218.index = 3218 := by decide

def c3218 : Contract := original3218.toContract.get (by decide)
theorem binding3218 : original3218.toContract = some c3218 := rfl

theorem checked3218 : check 4000 c3218 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3219 : RawOriginal := C025.records[19]'(by decide)
theorem original_id3219 : original3219.index = 3219 := by decide

def c3219 : Contract := original3219.toContract.get (by decide)
theorem binding3219 : original3219.toContract = some c3219 := rfl

theorem checked3219 : check 4000 c3219 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3220 : RawOriginal := C025.records[20]'(by decide)
theorem original_id3220 : original3220.index = 3220 := by decide

def c3220 : Contract := original3220.toContract.get (by decide)
theorem binding3220 : original3220.toContract = some c3220 := rfl

theorem checked3220 : check 4000 c3220 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3221 : RawOriginal := C025.records[21]'(by decide)
theorem original_id3221 : original3221.index = 3221 := by decide

def c3221 : Contract := original3221.toContract.get (by decide)
theorem binding3221 : original3221.toContract = some c3221 := rfl

theorem checked3221 : check 4000 c3221 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3206, c3206, 4000, checked3206⟩,
  ⟨3207, c3207, 4000, checked3207⟩,
  ⟨3208, c3208, 4000, checked3208⟩,
  ⟨3209, c3209, 4000, checked3209⟩,
  ⟨3210, c3210, 4000, checked3210⟩,
  ⟨3211, c3211, 4000, checked3211⟩,
  ⟨3212, c3212, 4000, checked3212⟩,
  ⟨3213, c3213, 4000, checked3213⟩,
  ⟨3214, c3214, 4000, checked3214⟩,
  ⟨3215, c3215, 4000, checked3215⟩,
  ⟨3216, c3216, 4000, checked3216⟩,
  ⟨3217, c3217, 4000, checked3217⟩,
  ⟨3218, c3218, 4000, checked3218⟩,
  ⟨3219, c3219, 4000, checked3219⟩,
  ⟨3220, c3220, 4000, checked3220⟩,
  ⟨3221, c3221, 4000, checked3221⟩]

end PA215.ContractShards.Shard025Part0
