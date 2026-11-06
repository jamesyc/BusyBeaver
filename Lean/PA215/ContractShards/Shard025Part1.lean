import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C025
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard025Part1
open PA215.Contracts PA215.Census

def original3222 : RawOriginal := C025.records[22]'(by decide)
theorem original_id3222 : original3222.index = 3222 := by decide

def c3222 : Contract := original3222.toContract.get (by decide)
theorem binding3222 : original3222.toContract = some c3222 := rfl

theorem checked3222 : check 4000 c3222 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3223 : RawOriginal := C025.records[23]'(by decide)
theorem original_id3223 : original3223.index = 3223 := by decide

def c3223 : Contract := original3223.toContract.get (by decide)
theorem binding3223 : original3223.toContract = some c3223 := rfl

theorem checked3223 : check 4000 c3223 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3224 : RawOriginal := C025.records[24]'(by decide)
theorem original_id3224 : original3224.index = 3224 := by decide

def c3224 : Contract := original3224.toContract.get (by decide)
theorem binding3224 : original3224.toContract = some c3224 := rfl

theorem checked3224 : check 4000 c3224 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3225 : RawOriginal := C025.records[25]'(by decide)
theorem original_id3225 : original3225.index = 3225 := by decide

def c3225 : Contract := original3225.toContract.get (by decide)
theorem binding3225 : original3225.toContract = some c3225 := rfl

theorem checked3225 : check 4000 c3225 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3226 : RawOriginal := C025.records[26]'(by decide)
theorem original_id3226 : original3226.index = 3226 := by decide

def c3226 : Contract := original3226.toContract.get (by decide)
theorem binding3226 : original3226.toContract = some c3226 := rfl

theorem checked3226 : check 4000 c3226 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3227 : RawOriginal := C025.records[27]'(by decide)
theorem original_id3227 : original3227.index = 3227 := by decide

def c3227 : Contract := original3227.toContract.get (by decide)
theorem binding3227 : original3227.toContract = some c3227 := rfl

theorem checked3227 : check 4000 c3227 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3228 : RawOriginal := C025.records[28]'(by decide)
theorem original_id3228 : original3228.index = 3228 := by decide

def c3228 : Contract := original3228.toContract.get (by decide)
theorem binding3228 : original3228.toContract = some c3228 := rfl

theorem checked3228 : check 4000 c3228 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3229 : RawOriginal := C025.records[29]'(by decide)
theorem original_id3229 : original3229.index = 3229 := by decide

def c3229 : Contract := original3229.toContract.get (by decide)
theorem binding3229 : original3229.toContract = some c3229 := rfl

theorem checked3229 : check 4000 c3229 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3230 : RawOriginal := C025.records[30]'(by decide)
theorem original_id3230 : original3230.index = 3230 := by decide

def c3230 : Contract := original3230.toContract.get (by decide)
theorem binding3230 : original3230.toContract = some c3230 := rfl

theorem checked3230 : check 4000 c3230 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3231 : RawOriginal := C025.records[31]'(by decide)
theorem original_id3231 : original3231.index = 3231 := by decide

def c3231 : Contract := original3231.toContract.get (by decide)
theorem binding3231 : original3231.toContract = some c3231 := rfl

theorem checked3231 : check 4000 c3231 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3232 : RawOriginal := C025.records[32]'(by decide)
theorem original_id3232 : original3232.index = 3232 := by decide

def c3232 : Contract := original3232.toContract.get (by decide)
theorem binding3232 : original3232.toContract = some c3232 := rfl

theorem checked3232 : check 4000 c3232 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3233 : RawOriginal := C025.records[33]'(by decide)
theorem original_id3233 : original3233.index = 3233 := by decide

def c3233 : Contract := original3233.toContract.get (by decide)
theorem binding3233 : original3233.toContract = some c3233 := rfl

theorem checked3233 : check 4000 c3233 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3234 : RawOriginal := C025.records[34]'(by decide)
theorem original_id3234 : original3234.index = 3234 := by decide

def c3234 : Contract := original3234.toContract.get (by decide)
theorem binding3234 : original3234.toContract = some c3234 := rfl

theorem checked3234 : check 4000 c3234 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3235 : RawOriginal := C025.records[35]'(by decide)
theorem original_id3235 : original3235.index = 3235 := by decide

def c3235 : Contract := original3235.toContract.get (by decide)
theorem binding3235 : original3235.toContract = some c3235 := rfl

theorem checked3235 : check 4000 c3235 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3236 : RawOriginal := C025.records[36]'(by decide)
theorem original_id3236 : original3236.index = 3236 := by decide

def c3236 : Contract := original3236.toContract.get (by decide)
theorem binding3236 : original3236.toContract = some c3236 := rfl

theorem checked3236 : check 4000 c3236 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3237 : RawOriginal := C025.records[37]'(by decide)
theorem original_id3237 : original3237.index = 3237 := by decide

def c3237 : Contract := original3237.toContract.get (by decide)
theorem binding3237 : original3237.toContract = some c3237 := rfl

theorem checked3237 : check 4000 c3237 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3222, c3222, 4000, checked3222⟩,
  ⟨3223, c3223, 4000, checked3223⟩,
  ⟨3224, c3224, 4000, checked3224⟩,
  ⟨3225, c3225, 4000, checked3225⟩,
  ⟨3226, c3226, 4000, checked3226⟩,
  ⟨3227, c3227, 4000, checked3227⟩,
  ⟨3228, c3228, 4000, checked3228⟩,
  ⟨3229, c3229, 4000, checked3229⟩,
  ⟨3230, c3230, 4000, checked3230⟩,
  ⟨3231, c3231, 4000, checked3231⟩,
  ⟨3232, c3232, 4000, checked3232⟩,
  ⟨3233, c3233, 4000, checked3233⟩,
  ⟨3234, c3234, 4000, checked3234⟩,
  ⟨3235, c3235, 4000, checked3235⟩,
  ⟨3236, c3236, 4000, checked3236⟩,
  ⟨3237, c3237, 4000, checked3237⟩]

end PA215.ContractShards.Shard025Part1
