import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C039
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard039Part2
open PA215.Contracts PA215.Census

def original5031 : RawOriginal := C039.records[39]'(by decide)
theorem original_id5031 : original5031.index = 5031 := by decide

def c5031 : Contract := original5031.toContract.get (by decide)
theorem binding5031 : original5031.toContract = some c5031 := rfl

theorem checked5031 : check 4000 c5031 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5032 : RawOriginal := C039.records[40]'(by decide)
theorem original_id5032 : original5032.index = 5032 := by decide

def c5032 : Contract := original5032.toContract.get (by decide)
theorem binding5032 : original5032.toContract = some c5032 := rfl

theorem checked5032 : check 4000 c5032 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5033 : RawOriginal := C039.records[41]'(by decide)
theorem original_id5033 : original5033.index = 5033 := by decide

def c5033 : Contract := original5033.toContract.get (by decide)
theorem binding5033 : original5033.toContract = some c5033 := rfl

theorem checked5033 : check 4000 c5033 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5034 : RawOriginal := C039.records[42]'(by decide)
theorem original_id5034 : original5034.index = 5034 := by decide

def c5034 : Contract := original5034.toContract.get (by decide)
theorem binding5034 : original5034.toContract = some c5034 := rfl

theorem checked5034 : check 4000 c5034 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5035 : RawOriginal := C039.records[43]'(by decide)
theorem original_id5035 : original5035.index = 5035 := by decide

def c5035 : Contract := original5035.toContract.get (by decide)
theorem binding5035 : original5035.toContract = some c5035 := rfl

theorem checked5035 : check 4000 c5035 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5036 : RawOriginal := C039.records[44]'(by decide)
theorem original_id5036 : original5036.index = 5036 := by decide

def c5036 : Contract := original5036.toContract.get (by decide)
theorem binding5036 : original5036.toContract = some c5036 := rfl

theorem checked5036 : check 4000 c5036 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5037 : RawOriginal := C039.records[45]'(by decide)
theorem original_id5037 : original5037.index = 5037 := by decide

def c5037 : Contract := original5037.toContract.get (by decide)
theorem binding5037 : original5037.toContract = some c5037 := rfl

theorem checked5037 : check 4000 c5037 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5038 : RawOriginal := C039.records[46]'(by decide)
theorem original_id5038 : original5038.index = 5038 := by decide

def c5038 : Contract := original5038.toContract.get (by decide)
theorem binding5038 : original5038.toContract = some c5038 := rfl

theorem checked5038 : check 4000 c5038 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5039 : RawOriginal := C039.records[47]'(by decide)
theorem original_id5039 : original5039.index = 5039 := by decide

def c5039 : Contract := original5039.toContract.get (by decide)
theorem binding5039 : original5039.toContract = some c5039 := rfl

theorem checked5039 : check 4000 c5039 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5040 : RawOriginal := C039.records[48]'(by decide)
theorem original_id5040 : original5040.index = 5040 := by decide

def c5040 : Contract := original5040.toContract.get (by decide)
theorem binding5040 : original5040.toContract = some c5040 := rfl

theorem checked5040 : check 4000 c5040 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5041 : RawOriginal := C039.records[49]'(by decide)
theorem original_id5041 : original5041.index = 5041 := by decide

def c5041 : Contract := original5041.toContract.get (by decide)
theorem binding5041 : original5041.toContract = some c5041 := rfl

theorem checked5041 : check 4000 c5041 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5042 : RawOriginal := C039.records[50]'(by decide)
theorem original_id5042 : original5042.index = 5042 := by decide

def c5042 : Contract := original5042.toContract.get (by decide)
theorem binding5042 : original5042.toContract = some c5042 := rfl

theorem checked5042 : check 4000 c5042 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5043 : RawOriginal := C039.records[51]'(by decide)
theorem original_id5043 : original5043.index = 5043 := by decide

def c5043 : Contract := original5043.toContract.get (by decide)
theorem binding5043 : original5043.toContract = some c5043 := rfl

theorem checked5043 : check 4000 c5043 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5044 : RawOriginal := C039.records[52]'(by decide)
theorem original_id5044 : original5044.index = 5044 := by decide

def c5044 : Contract := original5044.toContract.get (by decide)
theorem binding5044 : original5044.toContract = some c5044 := rfl

theorem checked5044 : check 4000 c5044 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5045 : RawOriginal := C039.records[53]'(by decide)
theorem original_id5045 : original5045.index = 5045 := by decide

def c5045 : Contract := original5045.toContract.get (by decide)
theorem binding5045 : original5045.toContract = some c5045 := rfl

theorem checked5045 : check 4000 c5045 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5046 : RawOriginal := C039.records[54]'(by decide)
theorem original_id5046 : original5046.index = 5046 := by decide

def c5046 : Contract := original5046.toContract.get (by decide)
theorem binding5046 : original5046.toContract = some c5046 := rfl

theorem checked5046 : check 4000 c5046 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨5031, c5031, 4000, checked5031⟩,
  ⟨5032, c5032, 4000, checked5032⟩,
  ⟨5033, c5033, 4000, checked5033⟩,
  ⟨5034, c5034, 4000, checked5034⟩,
  ⟨5035, c5035, 4000, checked5035⟩,
  ⟨5036, c5036, 4000, checked5036⟩,
  ⟨5037, c5037, 4000, checked5037⟩,
  ⟨5038, c5038, 4000, checked5038⟩,
  ⟨5039, c5039, 4000, checked5039⟩,
  ⟨5040, c5040, 4000, checked5040⟩,
  ⟨5041, c5041, 4000, checked5041⟩,
  ⟨5042, c5042, 4000, checked5042⟩,
  ⟨5043, c5043, 4000, checked5043⟩,
  ⟨5044, c5044, 4000, checked5044⟩,
  ⟨5045, c5045, 4000, checked5045⟩,
  ⟨5046, c5046, 4000, checked5046⟩]

end PA215.ContractShards.Shard039Part2
