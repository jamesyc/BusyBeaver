import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C024
import PA215.Census.C025
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard024Part7
open PA215.Contracts PA215.Census

def original3190 : RawOriginal := C024.records[118]'(by decide)
theorem original_id3190 : original3190.index = 3190 := by decide

def c3190 : Contract := original3190.toContract.get (by decide)
theorem binding3190 : original3190.toContract = some c3190 := rfl

theorem checked3190 : check 4000 c3190 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3191 : RawOriginal := C024.records[119]'(by decide)
theorem original_id3191 : original3191.index = 3191 := by decide

def c3191 : Contract := original3191.toContract.get (by decide)
theorem binding3191 : original3191.toContract = some c3191 := rfl

theorem checked3191 : check 4000 c3191 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3192 : RawOriginal := C024.records[120]'(by decide)
theorem original_id3192 : original3192.index = 3192 := by decide

def c3192 : Contract := original3192.toContract.get (by decide)
theorem binding3192 : original3192.toContract = some c3192 := rfl

theorem checked3192 : check 4000 c3192 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3193 : RawOriginal := C024.records[121]'(by decide)
theorem original_id3193 : original3193.index = 3193 := by decide

def c3193 : Contract := original3193.toContract.get (by decide)
theorem binding3193 : original3193.toContract = some c3193 := rfl

theorem checked3193 : check 4000 c3193 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3194 : RawOriginal := C024.records[122]'(by decide)
theorem original_id3194 : original3194.index = 3194 := by decide

def c3194 : Contract := original3194.toContract.get (by decide)
theorem binding3194 : original3194.toContract = some c3194 := rfl

theorem checked3194 : check 4000 c3194 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3195 : RawOriginal := C024.records[123]'(by decide)
theorem original_id3195 : original3195.index = 3195 := by decide

def c3195 : Contract := original3195.toContract.get (by decide)
theorem binding3195 : original3195.toContract = some c3195 := rfl

theorem checked3195 : check 4000 c3195 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3196 : RawOriginal := C024.records[124]'(by decide)
theorem original_id3196 : original3196.index = 3196 := by decide

def c3196 : Contract := original3196.toContract.get (by decide)
theorem binding3196 : original3196.toContract = some c3196 := rfl

theorem checked3196 : check 4000 c3196 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3197 : RawOriginal := C024.records[125]'(by decide)
theorem original_id3197 : original3197.index = 3197 := by decide

def c3197 : Contract := original3197.toContract.get (by decide)
theorem binding3197 : original3197.toContract = some c3197 := rfl

theorem checked3197 : check 4000 c3197 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3198 : RawOriginal := C024.records[126]'(by decide)
theorem original_id3198 : original3198.index = 3198 := by decide

def c3198 : Contract := original3198.toContract.get (by decide)
theorem binding3198 : original3198.toContract = some c3198 := rfl

theorem checked3198 : check 4000 c3198 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3199 : RawOriginal := C024.records[127]'(by decide)
theorem original_id3199 : original3199.index = 3199 := by decide

def c3199 : Contract := original3199.toContract.get (by decide)
theorem binding3199 : original3199.toContract = some c3199 := rfl

theorem checked3199 : check 4000 c3199 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3200 : RawOriginal := C025.records[0]'(by decide)
theorem original_id3200 : original3200.index = 3200 := by decide

def c3200 : Contract := original3200.toContract.get (by decide)
theorem binding3200 : original3200.toContract = some c3200 := rfl

theorem checked3200 : check 4000 c3200 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3201 : RawOriginal := C025.records[1]'(by decide)
theorem original_id3201 : original3201.index = 3201 := by decide

def c3201 : Contract := original3201.toContract.get (by decide)
theorem binding3201 : original3201.toContract = some c3201 := rfl

theorem checked3201 : check 4000 c3201 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3202 : RawOriginal := C025.records[2]'(by decide)
theorem original_id3202 : original3202.index = 3202 := by decide

def c3202 : Contract := original3202.toContract.get (by decide)
theorem binding3202 : original3202.toContract = some c3202 := rfl

theorem checked3202 : check 4000 c3202 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3203 : RawOriginal := C025.records[3]'(by decide)
theorem original_id3203 : original3203.index = 3203 := by decide

def c3203 : Contract := original3203.toContract.get (by decide)
theorem binding3203 : original3203.toContract = some c3203 := rfl

theorem checked3203 : check 4000 c3203 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3204 : RawOriginal := C025.records[4]'(by decide)
theorem original_id3204 : original3204.index = 3204 := by decide

def c3204 : Contract := original3204.toContract.get (by decide)
theorem binding3204 : original3204.toContract = some c3204 := rfl

theorem checked3204 : check 4000 c3204 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3205 : RawOriginal := C025.records[5]'(by decide)
theorem original_id3205 : original3205.index = 3205 := by decide

def c3205 : Contract := original3205.toContract.get (by decide)
theorem binding3205 : original3205.toContract = some c3205 := rfl

theorem checked3205 : check 4000 c3205 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3190, c3190, 4000, checked3190⟩,
  ⟨3191, c3191, 4000, checked3191⟩,
  ⟨3192, c3192, 4000, checked3192⟩,
  ⟨3193, c3193, 4000, checked3193⟩,
  ⟨3194, c3194, 4000, checked3194⟩,
  ⟨3195, c3195, 4000, checked3195⟩,
  ⟨3196, c3196, 4000, checked3196⟩,
  ⟨3197, c3197, 4000, checked3197⟩,
  ⟨3198, c3198, 4000, checked3198⟩,
  ⟨3199, c3199, 4000, checked3199⟩,
  ⟨3200, c3200, 4000, checked3200⟩,
  ⟨3201, c3201, 4000, checked3201⟩,
  ⟨3202, c3202, 4000, checked3202⟩,
  ⟨3203, c3203, 4000, checked3203⟩,
  ⟨3204, c3204, 4000, checked3204⟩,
  ⟨3205, c3205, 4000, checked3205⟩]

end PA215.ContractShards.Shard024Part7
