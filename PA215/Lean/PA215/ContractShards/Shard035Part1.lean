import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C035
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard035Part1
open PA215.Contracts PA215.Census

def original4502 : RawOriginal := C035.records[22]'(by decide)
theorem original_id4502 : original4502.index = 4502 := by decide

def c4502 : Contract := original4502.toContract.get (by decide)
theorem binding4502 : original4502.toContract = some c4502 := rfl

theorem checked4502 : check 4000 c4502 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4503 : RawOriginal := C035.records[23]'(by decide)
theorem original_id4503 : original4503.index = 4503 := by decide

def c4503 : Contract := original4503.toContract.get (by decide)
theorem binding4503 : original4503.toContract = some c4503 := rfl

theorem checked4503 : check 4000 c4503 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4504 : RawOriginal := C035.records[24]'(by decide)
theorem original_id4504 : original4504.index = 4504 := by decide

def c4504 : Contract := original4504.toContract.get (by decide)
theorem binding4504 : original4504.toContract = some c4504 := rfl

theorem checked4504 : check 4000 c4504 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4505 : RawOriginal := C035.records[25]'(by decide)
theorem original_id4505 : original4505.index = 4505 := by decide

def c4505 : Contract := original4505.toContract.get (by decide)
theorem binding4505 : original4505.toContract = some c4505 := rfl

theorem checked4505 : check 4000 c4505 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4506 : RawOriginal := C035.records[26]'(by decide)
theorem original_id4506 : original4506.index = 4506 := by decide

def c4506 : Contract := original4506.toContract.get (by decide)
theorem binding4506 : original4506.toContract = some c4506 := rfl

theorem checked4506 : check 4000 c4506 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4507 : RawOriginal := C035.records[27]'(by decide)
theorem original_id4507 : original4507.index = 4507 := by decide

def c4507 : Contract := original4507.toContract.get (by decide)
theorem binding4507 : original4507.toContract = some c4507 := rfl

theorem checked4507 : check 4000 c4507 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4508 : RawOriginal := C035.records[28]'(by decide)
theorem original_id4508 : original4508.index = 4508 := by decide

def c4508 : Contract := original4508.toContract.get (by decide)
theorem binding4508 : original4508.toContract = some c4508 := rfl

theorem checked4508 : check 4000 c4508 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4509 : RawOriginal := C035.records[29]'(by decide)
theorem original_id4509 : original4509.index = 4509 := by decide

def c4509 : Contract := original4509.toContract.get (by decide)
theorem binding4509 : original4509.toContract = some c4509 := rfl

theorem checked4509 : check 4000 c4509 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4510 : RawOriginal := C035.records[30]'(by decide)
theorem original_id4510 : original4510.index = 4510 := by decide

def c4510 : Contract := original4510.toContract.get (by decide)
theorem binding4510 : original4510.toContract = some c4510 := rfl

theorem checked4510 : check 4000 c4510 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4511 : RawOriginal := C035.records[31]'(by decide)
theorem original_id4511 : original4511.index = 4511 := by decide

def c4511 : Contract := original4511.toContract.get (by decide)
theorem binding4511 : original4511.toContract = some c4511 := rfl

theorem checked4511 : check 4000 c4511 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4512 : RawOriginal := C035.records[32]'(by decide)
theorem original_id4512 : original4512.index = 4512 := by decide

def c4512 : Contract := original4512.toContract.get (by decide)
theorem binding4512 : original4512.toContract = some c4512 := rfl

theorem checked4512 : check 4000 c4512 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4513 : RawOriginal := C035.records[33]'(by decide)
theorem original_id4513 : original4513.index = 4513 := by decide

def c4513 : Contract := original4513.toContract.get (by decide)
theorem binding4513 : original4513.toContract = some c4513 := rfl

theorem checked4513 : check 4000 c4513 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4514 : RawOriginal := C035.records[34]'(by decide)
theorem original_id4514 : original4514.index = 4514 := by decide

def c4514 : Contract := original4514.toContract.get (by decide)
theorem binding4514 : original4514.toContract = some c4514 := rfl

theorem checked4514 : check 4000 c4514 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4515 : RawOriginal := C035.records[35]'(by decide)
theorem original_id4515 : original4515.index = 4515 := by decide

def c4515 : Contract := original4515.toContract.get (by decide)
theorem binding4515 : original4515.toContract = some c4515 := rfl

theorem checked4515 : check 4000 c4515 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4516 : RawOriginal := C035.records[36]'(by decide)
theorem original_id4516 : original4516.index = 4516 := by decide

def c4516 : Contract := original4516.toContract.get (by decide)
theorem binding4516 : original4516.toContract = some c4516 := rfl

theorem checked4516 : check 4000 c4516 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4517 : RawOriginal := C035.records[37]'(by decide)
theorem original_id4517 : original4517.index = 4517 := by decide

def c4517 : Contract := original4517.toContract.get (by decide)
theorem binding4517 : original4517.toContract = some c4517 := rfl

theorem checked4517 : check 4000 c4517 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4502, c4502, 4000, checked4502⟩,
  ⟨4503, c4503, 4000, checked4503⟩,
  ⟨4504, c4504, 4000, checked4504⟩,
  ⟨4505, c4505, 4000, checked4505⟩,
  ⟨4506, c4506, 4000, checked4506⟩,
  ⟨4507, c4507, 4000, checked4507⟩,
  ⟨4508, c4508, 4000, checked4508⟩,
  ⟨4509, c4509, 4000, checked4509⟩,
  ⟨4510, c4510, 4000, checked4510⟩,
  ⟨4511, c4511, 4000, checked4511⟩,
  ⟨4512, c4512, 4000, checked4512⟩,
  ⟨4513, c4513, 4000, checked4513⟩,
  ⟨4514, c4514, 4000, checked4514⟩,
  ⟨4515, c4515, 4000, checked4515⟩,
  ⟨4516, c4516, 4000, checked4516⟩,
  ⟨4517, c4517, 4000, checked4517⟩]

end PA215.ContractShards.Shard035Part1
