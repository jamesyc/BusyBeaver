import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C023
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard023Part5
open PA215.Contracts PA215.Census

def original3030 : RawOriginal := C023.records[86]'(by decide)
theorem original_id3030 : original3030.index = 3030 := by decide

def c3030 : Contract := original3030.toContract.get (by decide)
theorem binding3030 : original3030.toContract = some c3030 := rfl

theorem checked3030 : check 4000 c3030 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3031 : RawOriginal := C023.records[87]'(by decide)
theorem original_id3031 : original3031.index = 3031 := by decide

def c3031 : Contract := original3031.toContract.get (by decide)
theorem binding3031 : original3031.toContract = some c3031 := rfl

theorem checked3031 : check 4000 c3031 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3032 : RawOriginal := C023.records[88]'(by decide)
theorem original_id3032 : original3032.index = 3032 := by decide

def c3032 : Contract := original3032.toContract.get (by decide)
theorem binding3032 : original3032.toContract = some c3032 := rfl

theorem checked3032 : check 4000 c3032 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3033 : RawOriginal := C023.records[89]'(by decide)
theorem original_id3033 : original3033.index = 3033 := by decide

def c3033 : Contract := original3033.toContract.get (by decide)
theorem binding3033 : original3033.toContract = some c3033 := rfl

theorem checked3033 : check 4000 c3033 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3034 : RawOriginal := C023.records[90]'(by decide)
theorem original_id3034 : original3034.index = 3034 := by decide

def c3034 : Contract := original3034.toContract.get (by decide)
theorem binding3034 : original3034.toContract = some c3034 := rfl

theorem checked3034 : check 4000 c3034 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3035 : RawOriginal := C023.records[91]'(by decide)
theorem original_id3035 : original3035.index = 3035 := by decide

def c3035 : Contract := original3035.toContract.get (by decide)
theorem binding3035 : original3035.toContract = some c3035 := rfl

theorem checked3035 : check 4000 c3035 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3036 : RawOriginal := C023.records[92]'(by decide)
theorem original_id3036 : original3036.index = 3036 := by decide

def c3036 : Contract := original3036.toContract.get (by decide)
theorem binding3036 : original3036.toContract = some c3036 := rfl

theorem checked3036 : check 4000 c3036 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3037 : RawOriginal := C023.records[93]'(by decide)
theorem original_id3037 : original3037.index = 3037 := by decide

def c3037 : Contract := original3037.toContract.get (by decide)
theorem binding3037 : original3037.toContract = some c3037 := rfl

theorem checked3037 : check 4000 c3037 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3038 : RawOriginal := C023.records[94]'(by decide)
theorem original_id3038 : original3038.index = 3038 := by decide

def c3038 : Contract := original3038.toContract.get (by decide)
theorem binding3038 : original3038.toContract = some c3038 := rfl

theorem checked3038 : check 4000 c3038 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3039 : RawOriginal := C023.records[95]'(by decide)
theorem original_id3039 : original3039.index = 3039 := by decide

def c3039 : Contract := original3039.toContract.get (by decide)
theorem binding3039 : original3039.toContract = some c3039 := rfl

theorem checked3039 : check 4000 c3039 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3040 : RawOriginal := C023.records[96]'(by decide)
theorem original_id3040 : original3040.index = 3040 := by decide

def c3040 : Contract := original3040.toContract.get (by decide)
theorem binding3040 : original3040.toContract = some c3040 := rfl

theorem checked3040 : check 4000 c3040 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3041 : RawOriginal := C023.records[97]'(by decide)
theorem original_id3041 : original3041.index = 3041 := by decide

def c3041 : Contract := original3041.toContract.get (by decide)
theorem binding3041 : original3041.toContract = some c3041 := rfl

theorem checked3041 : check 4000 c3041 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3042 : RawOriginal := C023.records[98]'(by decide)
theorem original_id3042 : original3042.index = 3042 := by decide

def c3042 : Contract := original3042.toContract.get (by decide)
theorem binding3042 : original3042.toContract = some c3042 := rfl

theorem checked3042 : check 4000 c3042 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3043 : RawOriginal := C023.records[99]'(by decide)
theorem original_id3043 : original3043.index = 3043 := by decide

def c3043 : Contract := original3043.toContract.get (by decide)
theorem binding3043 : original3043.toContract = some c3043 := rfl

theorem checked3043 : check 4000 c3043 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3044 : RawOriginal := C023.records[100]'(by decide)
theorem original_id3044 : original3044.index = 3044 := by decide

def c3044 : Contract := original3044.toContract.get (by decide)
theorem binding3044 : original3044.toContract = some c3044 := rfl

theorem checked3044 : check 4000 c3044 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3045 : RawOriginal := C023.records[101]'(by decide)
theorem original_id3045 : original3045.index = 3045 := by decide

def c3045 : Contract := original3045.toContract.get (by decide)
theorem binding3045 : original3045.toContract = some c3045 := rfl

theorem checked3045 : check 4000 c3045 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3030, c3030, 4000, checked3030⟩,
  ⟨3031, c3031, 4000, checked3031⟩,
  ⟨3032, c3032, 4000, checked3032⟩,
  ⟨3033, c3033, 4000, checked3033⟩,
  ⟨3034, c3034, 4000, checked3034⟩,
  ⟨3035, c3035, 4000, checked3035⟩,
  ⟨3036, c3036, 4000, checked3036⟩,
  ⟨3037, c3037, 4000, checked3037⟩,
  ⟨3038, c3038, 4000, checked3038⟩,
  ⟨3039, c3039, 4000, checked3039⟩,
  ⟨3040, c3040, 4000, checked3040⟩,
  ⟨3041, c3041, 4000, checked3041⟩,
  ⟨3042, c3042, 4000, checked3042⟩,
  ⟨3043, c3043, 4000, checked3043⟩,
  ⟨3044, c3044, 4000, checked3044⟩,
  ⟨3045, c3045, 4000, checked3045⟩]

end PA215.ContractShards.Shard023Part5
