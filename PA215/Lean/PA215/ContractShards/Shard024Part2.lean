import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C024
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard024Part2
open PA215.Contracts PA215.Census

def original3110 : RawOriginal := C024.records[38]'(by decide)
theorem original_id3110 : original3110.index = 3110 := by decide

def c3110 : Contract := original3110.toContract.get (by decide)
theorem binding3110 : original3110.toContract = some c3110 := rfl

theorem checked3110 : check 4000 c3110 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3111 : RawOriginal := C024.records[39]'(by decide)
theorem original_id3111 : original3111.index = 3111 := by decide

def c3111 : Contract := original3111.toContract.get (by decide)
theorem binding3111 : original3111.toContract = some c3111 := rfl

theorem checked3111 : check 4000 c3111 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3112 : RawOriginal := C024.records[40]'(by decide)
theorem original_id3112 : original3112.index = 3112 := by decide

def c3112 : Contract := original3112.toContract.get (by decide)
theorem binding3112 : original3112.toContract = some c3112 := rfl

theorem checked3112 : check 4000 c3112 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3113 : RawOriginal := C024.records[41]'(by decide)
theorem original_id3113 : original3113.index = 3113 := by decide

def c3113 : Contract := original3113.toContract.get (by decide)
theorem binding3113 : original3113.toContract = some c3113 := rfl

theorem checked3113 : check 4000 c3113 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3114 : RawOriginal := C024.records[42]'(by decide)
theorem original_id3114 : original3114.index = 3114 := by decide

def c3114 : Contract := original3114.toContract.get (by decide)
theorem binding3114 : original3114.toContract = some c3114 := rfl

theorem checked3114 : check 4000 c3114 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3115 : RawOriginal := C024.records[43]'(by decide)
theorem original_id3115 : original3115.index = 3115 := by decide

def c3115 : Contract := original3115.toContract.get (by decide)
theorem binding3115 : original3115.toContract = some c3115 := rfl

theorem checked3115 : check 4000 c3115 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3116 : RawOriginal := C024.records[44]'(by decide)
theorem original_id3116 : original3116.index = 3116 := by decide

def c3116 : Contract := original3116.toContract.get (by decide)
theorem binding3116 : original3116.toContract = some c3116 := rfl

theorem checked3116 : check 4000 c3116 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3117 : RawOriginal := C024.records[45]'(by decide)
theorem original_id3117 : original3117.index = 3117 := by decide

def c3117 : Contract := original3117.toContract.get (by decide)
theorem binding3117 : original3117.toContract = some c3117 := rfl

theorem checked3117 : check 4000 c3117 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3118 : RawOriginal := C024.records[46]'(by decide)
theorem original_id3118 : original3118.index = 3118 := by decide

def c3118 : Contract := original3118.toContract.get (by decide)
theorem binding3118 : original3118.toContract = some c3118 := rfl

theorem checked3118 : check 4000 c3118 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3119 : RawOriginal := C024.records[47]'(by decide)
theorem original_id3119 : original3119.index = 3119 := by decide

def c3119 : Contract := original3119.toContract.get (by decide)
theorem binding3119 : original3119.toContract = some c3119 := rfl

theorem checked3119 : check 4000 c3119 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3120 : RawOriginal := C024.records[48]'(by decide)
theorem original_id3120 : original3120.index = 3120 := by decide

def c3120 : Contract := original3120.toContract.get (by decide)
theorem binding3120 : original3120.toContract = some c3120 := rfl

theorem checked3120 : check 4000 c3120 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3121 : RawOriginal := C024.records[49]'(by decide)
theorem original_id3121 : original3121.index = 3121 := by decide

def c3121 : Contract := original3121.toContract.get (by decide)
theorem binding3121 : original3121.toContract = some c3121 := rfl

theorem checked3121 : check 4000 c3121 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3122 : RawOriginal := C024.records[50]'(by decide)
theorem original_id3122 : original3122.index = 3122 := by decide

def c3122 : Contract := original3122.toContract.get (by decide)
theorem binding3122 : original3122.toContract = some c3122 := rfl

theorem checked3122 : check 4000 c3122 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3123 : RawOriginal := C024.records[51]'(by decide)
theorem original_id3123 : original3123.index = 3123 := by decide

def c3123 : Contract := original3123.toContract.get (by decide)
theorem binding3123 : original3123.toContract = some c3123 := rfl

theorem checked3123 : check 4000 c3123 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3124 : RawOriginal := C024.records[52]'(by decide)
theorem original_id3124 : original3124.index = 3124 := by decide

def c3124 : Contract := original3124.toContract.get (by decide)
theorem binding3124 : original3124.toContract = some c3124 := rfl

theorem checked3124 : check 4000 c3124 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3125 : RawOriginal := C024.records[53]'(by decide)
theorem original_id3125 : original3125.index = 3125 := by decide

def c3125 : Contract := original3125.toContract.get (by decide)
theorem binding3125 : original3125.toContract = some c3125 := rfl

theorem checked3125 : check 4000 c3125 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3110, c3110, 4000, checked3110⟩,
  ⟨3111, c3111, 4000, checked3111⟩,
  ⟨3112, c3112, 4000, checked3112⟩,
  ⟨3113, c3113, 4000, checked3113⟩,
  ⟨3114, c3114, 4000, checked3114⟩,
  ⟨3115, c3115, 4000, checked3115⟩,
  ⟨3116, c3116, 4000, checked3116⟩,
  ⟨3117, c3117, 4000, checked3117⟩,
  ⟨3118, c3118, 4000, checked3118⟩,
  ⟨3119, c3119, 4000, checked3119⟩,
  ⟨3120, c3120, 4000, checked3120⟩,
  ⟨3121, c3121, 4000, checked3121⟩,
  ⟨3122, c3122, 4000, checked3122⟩,
  ⟨3123, c3123, 4000, checked3123⟩,
  ⟨3124, c3124, 4000, checked3124⟩,
  ⟨3125, c3125, 4000, checked3125⟩]

end PA215.ContractShards.Shard024Part2
