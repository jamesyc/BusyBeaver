import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C032
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard032Part3
open PA215.Contracts PA215.Census

def original4150 : RawOriginal := C032.records[54]'(by decide)
theorem original_id4150 : original4150.index = 4150 := by decide

def c4150 : Contract := original4150.toContract.get (by decide)
theorem binding4150 : original4150.toContract = some c4150 := rfl

theorem checked4150 : check 4000 c4150 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4151 : RawOriginal := C032.records[55]'(by decide)
theorem original_id4151 : original4151.index = 4151 := by decide

def c4151 : Contract := original4151.toContract.get (by decide)
theorem binding4151 : original4151.toContract = some c4151 := rfl

theorem checked4151 : check 4000 c4151 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4152 : RawOriginal := C032.records[56]'(by decide)
theorem original_id4152 : original4152.index = 4152 := by decide

def c4152 : Contract := original4152.toContract.get (by decide)
theorem binding4152 : original4152.toContract = some c4152 := rfl

theorem checked4152 : check 4000 c4152 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4153 : RawOriginal := C032.records[57]'(by decide)
theorem original_id4153 : original4153.index = 4153 := by decide

def c4153 : Contract := original4153.toContract.get (by decide)
theorem binding4153 : original4153.toContract = some c4153 := rfl

theorem checked4153 : check 4000 c4153 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4154 : RawOriginal := C032.records[58]'(by decide)
theorem original_id4154 : original4154.index = 4154 := by decide

def c4154 : Contract := original4154.toContract.get (by decide)
theorem binding4154 : original4154.toContract = some c4154 := rfl

theorem checked4154 : check 4000 c4154 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4155 : RawOriginal := C032.records[59]'(by decide)
theorem original_id4155 : original4155.index = 4155 := by decide

def c4155 : Contract := original4155.toContract.get (by decide)
theorem binding4155 : original4155.toContract = some c4155 := rfl

theorem checked4155 : check 4000 c4155 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4156 : RawOriginal := C032.records[60]'(by decide)
theorem original_id4156 : original4156.index = 4156 := by decide

def c4156 : Contract := original4156.toContract.get (by decide)
theorem binding4156 : original4156.toContract = some c4156 := rfl

theorem checked4156 : check 4000 c4156 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4157 : RawOriginal := C032.records[61]'(by decide)
theorem original_id4157 : original4157.index = 4157 := by decide

def c4157 : Contract := original4157.toContract.get (by decide)
theorem binding4157 : original4157.toContract = some c4157 := rfl

theorem checked4157 : check 4000 c4157 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4158 : RawOriginal := C032.records[62]'(by decide)
theorem original_id4158 : original4158.index = 4158 := by decide

def c4158 : Contract := original4158.toContract.get (by decide)
theorem binding4158 : original4158.toContract = some c4158 := rfl

theorem checked4158 : check 4000 c4158 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4159 : RawOriginal := C032.records[63]'(by decide)
theorem original_id4159 : original4159.index = 4159 := by decide

def c4159 : Contract := original4159.toContract.get (by decide)
theorem binding4159 : original4159.toContract = some c4159 := rfl

theorem checked4159 : check 4000 c4159 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4160 : RawOriginal := C032.records[64]'(by decide)
theorem original_id4160 : original4160.index = 4160 := by decide

def c4160 : Contract := original4160.toContract.get (by decide)
theorem binding4160 : original4160.toContract = some c4160 := rfl

theorem checked4160 : check 4000 c4160 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4161 : RawOriginal := C032.records[65]'(by decide)
theorem original_id4161 : original4161.index = 4161 := by decide

def c4161 : Contract := original4161.toContract.get (by decide)
theorem binding4161 : original4161.toContract = some c4161 := rfl

theorem checked4161 : check 4000 c4161 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4162 : RawOriginal := C032.records[66]'(by decide)
theorem original_id4162 : original4162.index = 4162 := by decide

def c4162 : Contract := original4162.toContract.get (by decide)
theorem binding4162 : original4162.toContract = some c4162 := rfl

theorem checked4162 : check 4000 c4162 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4163 : RawOriginal := C032.records[67]'(by decide)
theorem original_id4163 : original4163.index = 4163 := by decide

def c4163 : Contract := original4163.toContract.get (by decide)
theorem binding4163 : original4163.toContract = some c4163 := rfl

theorem checked4163 : check 4000 c4163 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4164 : RawOriginal := C032.records[68]'(by decide)
theorem original_id4164 : original4164.index = 4164 := by decide

def c4164 : Contract := original4164.toContract.get (by decide)
theorem binding4164 : original4164.toContract = some c4164 := rfl

theorem checked4164 : check 4000 c4164 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4165 : RawOriginal := C032.records[69]'(by decide)
theorem original_id4165 : original4165.index = 4165 := by decide

def c4165 : Contract := original4165.toContract.get (by decide)
theorem binding4165 : original4165.toContract = some c4165 := rfl

theorem checked4165 : check 4000 c4165 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4150, c4150, 4000, checked4150⟩,
  ⟨4151, c4151, 4000, checked4151⟩,
  ⟨4152, c4152, 4000, checked4152⟩,
  ⟨4153, c4153, 4000, checked4153⟩,
  ⟨4154, c4154, 4000, checked4154⟩,
  ⟨4155, c4155, 4000, checked4155⟩,
  ⟨4156, c4156, 4000, checked4156⟩,
  ⟨4157, c4157, 4000, checked4157⟩,
  ⟨4158, c4158, 4000, checked4158⟩,
  ⟨4159, c4159, 4000, checked4159⟩,
  ⟨4160, c4160, 4000, checked4160⟩,
  ⟨4161, c4161, 4000, checked4161⟩,
  ⟨4162, c4162, 4000, checked4162⟩,
  ⟨4163, c4163, 4000, checked4163⟩,
  ⟨4164, c4164, 4000, checked4164⟩,
  ⟨4165, c4165, 4000, checked4165⟩]

end PA215.ContractShards.Shard032Part3
