import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C024
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard024Part1
open PA215.Contracts PA215.Census

def original3094 : RawOriginal := C024.records[22]'(by decide)
theorem original_id3094 : original3094.index = 3094 := by decide

def c3094 : Contract := original3094.toContract.get (by decide)
theorem binding3094 : original3094.toContract = some c3094 := rfl

theorem checked3094 : check 4000 c3094 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3095 : RawOriginal := C024.records[23]'(by decide)
theorem original_id3095 : original3095.index = 3095 := by decide

def c3095 : Contract := original3095.toContract.get (by decide)
theorem binding3095 : original3095.toContract = some c3095 := rfl

theorem checked3095 : check 4000 c3095 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3096 : RawOriginal := C024.records[24]'(by decide)
theorem original_id3096 : original3096.index = 3096 := by decide

def c3096 : Contract := original3096.toContract.get (by decide)
theorem binding3096 : original3096.toContract = some c3096 := rfl

theorem checked3096 : check 4000 c3096 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3097 : RawOriginal := C024.records[25]'(by decide)
theorem original_id3097 : original3097.index = 3097 := by decide

def c3097 : Contract := original3097.toContract.get (by decide)
theorem binding3097 : original3097.toContract = some c3097 := rfl

theorem checked3097 : check 4000 c3097 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3098 : RawOriginal := C024.records[26]'(by decide)
theorem original_id3098 : original3098.index = 3098 := by decide

def c3098 : Contract := original3098.toContract.get (by decide)
theorem binding3098 : original3098.toContract = some c3098 := rfl

theorem checked3098 : check 4000 c3098 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3099 : RawOriginal := C024.records[27]'(by decide)
theorem original_id3099 : original3099.index = 3099 := by decide

def c3099 : Contract := original3099.toContract.get (by decide)
theorem binding3099 : original3099.toContract = some c3099 := rfl

theorem checked3099 : check 4000 c3099 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3100 : RawOriginal := C024.records[28]'(by decide)
theorem original_id3100 : original3100.index = 3100 := by decide

def c3100 : Contract := original3100.toContract.get (by decide)
theorem binding3100 : original3100.toContract = some c3100 := rfl

theorem checked3100 : check 4000 c3100 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3101 : RawOriginal := C024.records[29]'(by decide)
theorem original_id3101 : original3101.index = 3101 := by decide

def c3101 : Contract := original3101.toContract.get (by decide)
theorem binding3101 : original3101.toContract = some c3101 := rfl

theorem checked3101 : check 4000 c3101 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3102 : RawOriginal := C024.records[30]'(by decide)
theorem original_id3102 : original3102.index = 3102 := by decide

def c3102 : Contract := original3102.toContract.get (by decide)
theorem binding3102 : original3102.toContract = some c3102 := rfl

theorem checked3102 : check 4000 c3102 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3103 : RawOriginal := C024.records[31]'(by decide)
theorem original_id3103 : original3103.index = 3103 := by decide

def c3103 : Contract := original3103.toContract.get (by decide)
theorem binding3103 : original3103.toContract = some c3103 := rfl

theorem checked3103 : check 4000 c3103 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3104 : RawOriginal := C024.records[32]'(by decide)
theorem original_id3104 : original3104.index = 3104 := by decide

def c3104 : Contract := original3104.toContract.get (by decide)
theorem binding3104 : original3104.toContract = some c3104 := rfl

theorem checked3104 : check 4000 c3104 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3105 : RawOriginal := C024.records[33]'(by decide)
theorem original_id3105 : original3105.index = 3105 := by decide

def c3105 : Contract := original3105.toContract.get (by decide)
theorem binding3105 : original3105.toContract = some c3105 := rfl

theorem checked3105 : check 4000 c3105 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3106 : RawOriginal := C024.records[34]'(by decide)
theorem original_id3106 : original3106.index = 3106 := by decide

def c3106 : Contract := original3106.toContract.get (by decide)
theorem binding3106 : original3106.toContract = some c3106 := rfl

theorem checked3106 : check 4000 c3106 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3107 : RawOriginal := C024.records[35]'(by decide)
theorem original_id3107 : original3107.index = 3107 := by decide

def c3107 : Contract := original3107.toContract.get (by decide)
theorem binding3107 : original3107.toContract = some c3107 := rfl

theorem checked3107 : check 4000 c3107 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3108 : RawOriginal := C024.records[36]'(by decide)
theorem original_id3108 : original3108.index = 3108 := by decide

def c3108 : Contract := original3108.toContract.get (by decide)
theorem binding3108 : original3108.toContract = some c3108 := rfl

theorem checked3108 : check 4000 c3108 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3109 : RawOriginal := C024.records[37]'(by decide)
theorem original_id3109 : original3109.index = 3109 := by decide

def c3109 : Contract := original3109.toContract.get (by decide)
theorem binding3109 : original3109.toContract = some c3109 := rfl

theorem checked3109 : check 4000 c3109 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3094, c3094, 4000, checked3094⟩,
  ⟨3095, c3095, 4000, checked3095⟩,
  ⟨3096, c3096, 4000, checked3096⟩,
  ⟨3097, c3097, 4000, checked3097⟩,
  ⟨3098, c3098, 4000, checked3098⟩,
  ⟨3099, c3099, 4000, checked3099⟩,
  ⟨3100, c3100, 4000, checked3100⟩,
  ⟨3101, c3101, 4000, checked3101⟩,
  ⟨3102, c3102, 4000, checked3102⟩,
  ⟨3103, c3103, 4000, checked3103⟩,
  ⟨3104, c3104, 4000, checked3104⟩,
  ⟨3105, c3105, 4000, checked3105⟩,
  ⟨3106, c3106, 4000, checked3106⟩,
  ⟨3107, c3107, 4000, checked3107⟩,
  ⟨3108, c3108, 4000, checked3108⟩,
  ⟨3109, c3109, 4000, checked3109⟩]

end PA215.ContractShards.Shard024Part1
