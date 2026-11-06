import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C023
import PA215.Census.C024
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard023Part7
open PA215.Contracts PA215.Census

def original3062 : RawOriginal := C023.records[118]'(by decide)
theorem original_id3062 : original3062.index = 3062 := by decide

def c3062 : Contract := original3062.toContract.get (by decide)
theorem binding3062 : original3062.toContract = some c3062 := rfl

theorem checked3062 : check 4000 c3062 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3063 : RawOriginal := C023.records[119]'(by decide)
theorem original_id3063 : original3063.index = 3063 := by decide

def c3063 : Contract := original3063.toContract.get (by decide)
theorem binding3063 : original3063.toContract = some c3063 := rfl

theorem checked3063 : check 4000 c3063 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3064 : RawOriginal := C023.records[120]'(by decide)
theorem original_id3064 : original3064.index = 3064 := by decide

def c3064 : Contract := original3064.toContract.get (by decide)
theorem binding3064 : original3064.toContract = some c3064 := rfl

theorem checked3064 : check 4000 c3064 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3065 : RawOriginal := C023.records[121]'(by decide)
theorem original_id3065 : original3065.index = 3065 := by decide

def c3065 : Contract := original3065.toContract.get (by decide)
theorem binding3065 : original3065.toContract = some c3065 := rfl

theorem checked3065 : check 4000 c3065 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3066 : RawOriginal := C023.records[122]'(by decide)
theorem original_id3066 : original3066.index = 3066 := by decide

def c3066 : Contract := original3066.toContract.get (by decide)
theorem binding3066 : original3066.toContract = some c3066 := rfl

theorem checked3066 : check 4000 c3066 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3067 : RawOriginal := C023.records[123]'(by decide)
theorem original_id3067 : original3067.index = 3067 := by decide

def c3067 : Contract := original3067.toContract.get (by decide)
theorem binding3067 : original3067.toContract = some c3067 := rfl

theorem checked3067 : check 4000 c3067 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3068 : RawOriginal := C023.records[124]'(by decide)
theorem original_id3068 : original3068.index = 3068 := by decide

def c3068 : Contract := original3068.toContract.get (by decide)
theorem binding3068 : original3068.toContract = some c3068 := rfl

theorem checked3068 : check 4000 c3068 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3069 : RawOriginal := C023.records[125]'(by decide)
theorem original_id3069 : original3069.index = 3069 := by decide

def c3069 : Contract := original3069.toContract.get (by decide)
theorem binding3069 : original3069.toContract = some c3069 := rfl

theorem checked3069 : check 4000 c3069 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3070 : RawOriginal := C023.records[126]'(by decide)
theorem original_id3070 : original3070.index = 3070 := by decide

def c3070 : Contract := original3070.toContract.get (by decide)
theorem binding3070 : original3070.toContract = some c3070 := rfl

theorem checked3070 : check 4000 c3070 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3071 : RawOriginal := C023.records[127]'(by decide)
theorem original_id3071 : original3071.index = 3071 := by decide

def c3071 : Contract := original3071.toContract.get (by decide)
theorem binding3071 : original3071.toContract = some c3071 := rfl

theorem checked3071 : check 4000 c3071 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3072 : RawOriginal := C024.records[0]'(by decide)
theorem original_id3072 : original3072.index = 3072 := by decide

def c3072 : Contract := original3072.toContract.get (by decide)
theorem binding3072 : original3072.toContract = some c3072 := rfl

theorem checked3072 : check 4000 c3072 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3073 : RawOriginal := C024.records[1]'(by decide)
theorem original_id3073 : original3073.index = 3073 := by decide

def c3073 : Contract := original3073.toContract.get (by decide)
theorem binding3073 : original3073.toContract = some c3073 := rfl

theorem checked3073 : check 4000 c3073 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3074 : RawOriginal := C024.records[2]'(by decide)
theorem original_id3074 : original3074.index = 3074 := by decide

def c3074 : Contract := original3074.toContract.get (by decide)
theorem binding3074 : original3074.toContract = some c3074 := rfl

theorem checked3074 : check 4000 c3074 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3075 : RawOriginal := C024.records[3]'(by decide)
theorem original_id3075 : original3075.index = 3075 := by decide

def c3075 : Contract := original3075.toContract.get (by decide)
theorem binding3075 : original3075.toContract = some c3075 := rfl

theorem checked3075 : check 4000 c3075 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3076 : RawOriginal := C024.records[4]'(by decide)
theorem original_id3076 : original3076.index = 3076 := by decide

def c3076 : Contract := original3076.toContract.get (by decide)
theorem binding3076 : original3076.toContract = some c3076 := rfl

theorem checked3076 : check 4000 c3076 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3077 : RawOriginal := C024.records[5]'(by decide)
theorem original_id3077 : original3077.index = 3077 := by decide

def c3077 : Contract := original3077.toContract.get (by decide)
theorem binding3077 : original3077.toContract = some c3077 := rfl

theorem checked3077 : check 4000 c3077 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3062, c3062, 4000, checked3062⟩,
  ⟨3063, c3063, 4000, checked3063⟩,
  ⟨3064, c3064, 4000, checked3064⟩,
  ⟨3065, c3065, 4000, checked3065⟩,
  ⟨3066, c3066, 4000, checked3066⟩,
  ⟨3067, c3067, 4000, checked3067⟩,
  ⟨3068, c3068, 4000, checked3068⟩,
  ⟨3069, c3069, 4000, checked3069⟩,
  ⟨3070, c3070, 4000, checked3070⟩,
  ⟨3071, c3071, 4000, checked3071⟩,
  ⟨3072, c3072, 4000, checked3072⟩,
  ⟨3073, c3073, 4000, checked3073⟩,
  ⟨3074, c3074, 4000, checked3074⟩,
  ⟨3075, c3075, 4000, checked3075⟩,
  ⟨3076, c3076, 4000, checked3076⟩,
  ⟨3077, c3077, 4000, checked3077⟩]

end PA215.ContractShards.Shard023Part7
