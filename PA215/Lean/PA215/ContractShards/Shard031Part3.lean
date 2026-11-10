import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C031
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard031Part3
open PA215.Contracts PA215.Census

def original4022 : RawOriginal := C031.records[54]'(by decide)
theorem original_id4022 : original4022.index = 4022 := by decide

def c4022 : Contract := original4022.toContract.get (by decide)
theorem binding4022 : original4022.toContract = some c4022 := rfl

theorem checked4022 : check 4000 c4022 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4023 : RawOriginal := C031.records[55]'(by decide)
theorem original_id4023 : original4023.index = 4023 := by decide

def c4023 : Contract := original4023.toContract.get (by decide)
theorem binding4023 : original4023.toContract = some c4023 := rfl

theorem checked4023 : check 4000 c4023 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4024 : RawOriginal := C031.records[56]'(by decide)
theorem original_id4024 : original4024.index = 4024 := by decide

def c4024 : Contract := original4024.toContract.get (by decide)
theorem binding4024 : original4024.toContract = some c4024 := rfl

theorem checked4024 : check 4000 c4024 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4025 : RawOriginal := C031.records[57]'(by decide)
theorem original_id4025 : original4025.index = 4025 := by decide

def c4025 : Contract := original4025.toContract.get (by decide)
theorem binding4025 : original4025.toContract = some c4025 := rfl

theorem checked4025 : check 4000 c4025 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4026 : RawOriginal := C031.records[58]'(by decide)
theorem original_id4026 : original4026.index = 4026 := by decide

def c4026 : Contract := original4026.toContract.get (by decide)
theorem binding4026 : original4026.toContract = some c4026 := rfl

theorem checked4026 : check 4000 c4026 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4027 : RawOriginal := C031.records[59]'(by decide)
theorem original_id4027 : original4027.index = 4027 := by decide

def c4027 : Contract := original4027.toContract.get (by decide)
theorem binding4027 : original4027.toContract = some c4027 := rfl

theorem checked4027 : check 4000 c4027 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4028 : RawOriginal := C031.records[60]'(by decide)
theorem original_id4028 : original4028.index = 4028 := by decide

def c4028 : Contract := original4028.toContract.get (by decide)
theorem binding4028 : original4028.toContract = some c4028 := rfl

theorem checked4028 : check 4000 c4028 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4029 : RawOriginal := C031.records[61]'(by decide)
theorem original_id4029 : original4029.index = 4029 := by decide

def c4029 : Contract := original4029.toContract.get (by decide)
theorem binding4029 : original4029.toContract = some c4029 := rfl

theorem checked4029 : check 4000 c4029 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4030 : RawOriginal := C031.records[62]'(by decide)
theorem original_id4030 : original4030.index = 4030 := by decide

def c4030 : Contract := original4030.toContract.get (by decide)
theorem binding4030 : original4030.toContract = some c4030 := rfl

theorem checked4030 : check 4000 c4030 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4031 : RawOriginal := C031.records[63]'(by decide)
theorem original_id4031 : original4031.index = 4031 := by decide

def c4031 : Contract := original4031.toContract.get (by decide)
theorem binding4031 : original4031.toContract = some c4031 := rfl

theorem checked4031 : check 4000 c4031 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4032 : RawOriginal := C031.records[64]'(by decide)
theorem original_id4032 : original4032.index = 4032 := by decide

def c4032 : Contract := original4032.toContract.get (by decide)
theorem binding4032 : original4032.toContract = some c4032 := rfl

theorem checked4032 : check 4000 c4032 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4033 : RawOriginal := C031.records[65]'(by decide)
theorem original_id4033 : original4033.index = 4033 := by decide

def c4033 : Contract := original4033.toContract.get (by decide)
theorem binding4033 : original4033.toContract = some c4033 := rfl

theorem checked4033 : check 4000 c4033 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4034 : RawOriginal := C031.records[66]'(by decide)
theorem original_id4034 : original4034.index = 4034 := by decide

def c4034 : Contract := original4034.toContract.get (by decide)
theorem binding4034 : original4034.toContract = some c4034 := rfl

theorem checked4034 : check 4000 c4034 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4035 : RawOriginal := C031.records[67]'(by decide)
theorem original_id4035 : original4035.index = 4035 := by decide

def c4035 : Contract := original4035.toContract.get (by decide)
theorem binding4035 : original4035.toContract = some c4035 := rfl

theorem checked4035 : check 4000 c4035 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4036 : RawOriginal := C031.records[68]'(by decide)
theorem original_id4036 : original4036.index = 4036 := by decide

def c4036 : Contract := original4036.toContract.get (by decide)
theorem binding4036 : original4036.toContract = some c4036 := rfl

theorem checked4036 : check 4000 c4036 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4037 : RawOriginal := C031.records[69]'(by decide)
theorem original_id4037 : original4037.index = 4037 := by decide

def c4037 : Contract := original4037.toContract.get (by decide)
theorem binding4037 : original4037.toContract = some c4037 := rfl

theorem checked4037 : check 4000 c4037 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4022, c4022, 4000, checked4022⟩,
  ⟨4023, c4023, 4000, checked4023⟩,
  ⟨4024, c4024, 4000, checked4024⟩,
  ⟨4025, c4025, 4000, checked4025⟩,
  ⟨4026, c4026, 4000, checked4026⟩,
  ⟨4027, c4027, 4000, checked4027⟩,
  ⟨4028, c4028, 4000, checked4028⟩,
  ⟨4029, c4029, 4000, checked4029⟩,
  ⟨4030, c4030, 4000, checked4030⟩,
  ⟨4031, c4031, 4000, checked4031⟩,
  ⟨4032, c4032, 4000, checked4032⟩,
  ⟨4033, c4033, 4000, checked4033⟩,
  ⟨4034, c4034, 4000, checked4034⟩,
  ⟨4035, c4035, 4000, checked4035⟩,
  ⟨4036, c4036, 4000, checked4036⟩,
  ⟨4037, c4037, 4000, checked4037⟩]

end PA215.ContractShards.Shard031Part3
