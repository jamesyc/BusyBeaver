import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C025
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard025Part6
open PA215.Contracts PA215.Census

def original3302 : RawOriginal := C025.records[102]'(by decide)
theorem original_id3302 : original3302.index = 3302 := by decide

def c3302 : Contract := original3302.toContract.get (by decide)
theorem binding3302 : original3302.toContract = some c3302 := rfl

theorem checked3302 : check 4000 c3302 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3303 : RawOriginal := C025.records[103]'(by decide)
theorem original_id3303 : original3303.index = 3303 := by decide

def c3303 : Contract := original3303.toContract.get (by decide)
theorem binding3303 : original3303.toContract = some c3303 := rfl

theorem checked3303 : check 4000 c3303 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3304 : RawOriginal := C025.records[104]'(by decide)
theorem original_id3304 : original3304.index = 3304 := by decide

def c3304 : Contract := original3304.toContract.get (by decide)
theorem binding3304 : original3304.toContract = some c3304 := rfl

theorem checked3304 : check 4000 c3304 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3305 : RawOriginal := C025.records[105]'(by decide)
theorem original_id3305 : original3305.index = 3305 := by decide

def c3305 : Contract := original3305.toContract.get (by decide)
theorem binding3305 : original3305.toContract = some c3305 := rfl

theorem checked3305 : check 4000 c3305 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3306 : RawOriginal := C025.records[106]'(by decide)
theorem original_id3306 : original3306.index = 3306 := by decide

def c3306 : Contract := original3306.toContract.get (by decide)
theorem binding3306 : original3306.toContract = some c3306 := rfl

theorem checked3306 : check 4000 c3306 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3307 : RawOriginal := C025.records[107]'(by decide)
theorem original_id3307 : original3307.index = 3307 := by decide

def c3307 : Contract := original3307.toContract.get (by decide)
theorem binding3307 : original3307.toContract = some c3307 := rfl

theorem checked3307 : check 4000 c3307 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3308 : RawOriginal := C025.records[108]'(by decide)
theorem original_id3308 : original3308.index = 3308 := by decide

def c3308 : Contract := original3308.toContract.get (by decide)
theorem binding3308 : original3308.toContract = some c3308 := rfl

theorem checked3308 : check 4000 c3308 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3309 : RawOriginal := C025.records[109]'(by decide)
theorem original_id3309 : original3309.index = 3309 := by decide

def c3309 : Contract := original3309.toContract.get (by decide)
theorem binding3309 : original3309.toContract = some c3309 := rfl

theorem checked3309 : check 4000 c3309 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3310 : RawOriginal := C025.records[110]'(by decide)
theorem original_id3310 : original3310.index = 3310 := by decide

def c3310 : Contract := original3310.toContract.get (by decide)
theorem binding3310 : original3310.toContract = some c3310 := rfl

theorem checked3310 : check 4000 c3310 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3311 : RawOriginal := C025.records[111]'(by decide)
theorem original_id3311 : original3311.index = 3311 := by decide

def c3311 : Contract := original3311.toContract.get (by decide)
theorem binding3311 : original3311.toContract = some c3311 := rfl

theorem checked3311 : check 4000 c3311 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3312 : RawOriginal := C025.records[112]'(by decide)
theorem original_id3312 : original3312.index = 3312 := by decide

def c3312 : Contract := original3312.toContract.get (by decide)
theorem binding3312 : original3312.toContract = some c3312 := rfl

theorem checked3312 : check 4000 c3312 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3313 : RawOriginal := C025.records[113]'(by decide)
theorem original_id3313 : original3313.index = 3313 := by decide

def c3313 : Contract := original3313.toContract.get (by decide)
theorem binding3313 : original3313.toContract = some c3313 := rfl

theorem checked3313 : check 4000 c3313 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3314 : RawOriginal := C025.records[114]'(by decide)
theorem original_id3314 : original3314.index = 3314 := by decide

def c3314 : Contract := original3314.toContract.get (by decide)
theorem binding3314 : original3314.toContract = some c3314 := rfl

theorem checked3314 : check 4000 c3314 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3315 : RawOriginal := C025.records[115]'(by decide)
theorem original_id3315 : original3315.index = 3315 := by decide

def c3315 : Contract := original3315.toContract.get (by decide)
theorem binding3315 : original3315.toContract = some c3315 := rfl

theorem checked3315 : check 4000 c3315 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3316 : RawOriginal := C025.records[116]'(by decide)
theorem original_id3316 : original3316.index = 3316 := by decide

def c3316 : Contract := original3316.toContract.get (by decide)
theorem binding3316 : original3316.toContract = some c3316 := rfl

theorem checked3316 : check 4000 c3316 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3317 : RawOriginal := C025.records[117]'(by decide)
theorem original_id3317 : original3317.index = 3317 := by decide

def c3317 : Contract := original3317.toContract.get (by decide)
theorem binding3317 : original3317.toContract = some c3317 := rfl

theorem checked3317 : check 4000 c3317 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3302, c3302, 4000, checked3302⟩,
  ⟨3303, c3303, 4000, checked3303⟩,
  ⟨3304, c3304, 4000, checked3304⟩,
  ⟨3305, c3305, 4000, checked3305⟩,
  ⟨3306, c3306, 4000, checked3306⟩,
  ⟨3307, c3307, 4000, checked3307⟩,
  ⟨3308, c3308, 4000, checked3308⟩,
  ⟨3309, c3309, 4000, checked3309⟩,
  ⟨3310, c3310, 4000, checked3310⟩,
  ⟨3311, c3311, 4000, checked3311⟩,
  ⟨3312, c3312, 4000, checked3312⟩,
  ⟨3313, c3313, 4000, checked3313⟩,
  ⟨3314, c3314, 4000, checked3314⟩,
  ⟨3315, c3315, 4000, checked3315⟩,
  ⟨3316, c3316, 4000, checked3316⟩,
  ⟨3317, c3317, 4000, checked3317⟩]

end PA215.ContractShards.Shard025Part6
