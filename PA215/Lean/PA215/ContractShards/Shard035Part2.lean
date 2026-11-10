import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C035
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard035Part2
open PA215.Contracts PA215.Census

def original4518 : RawOriginal := C035.records[38]'(by decide)
theorem original_id4518 : original4518.index = 4518 := by decide

def c4518 : Contract := original4518.toContract.get (by decide)
theorem binding4518 : original4518.toContract = some c4518 := rfl

theorem checked4518 : check 4000 c4518 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4519 : RawOriginal := C035.records[39]'(by decide)
theorem original_id4519 : original4519.index = 4519 := by decide

def c4519 : Contract := original4519.toContract.get (by decide)
theorem binding4519 : original4519.toContract = some c4519 := rfl

theorem checked4519 : check 4000 c4519 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4520 : RawOriginal := C035.records[40]'(by decide)
theorem original_id4520 : original4520.index = 4520 := by decide

def c4520 : Contract := original4520.toContract.get (by decide)
theorem binding4520 : original4520.toContract = some c4520 := rfl

theorem checked4520 : check 4000 c4520 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4521 : RawOriginal := C035.records[41]'(by decide)
theorem original_id4521 : original4521.index = 4521 := by decide

def c4521 : Contract := original4521.toContract.get (by decide)
theorem binding4521 : original4521.toContract = some c4521 := rfl

theorem checked4521 : check 4000 c4521 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4522 : RawOriginal := C035.records[42]'(by decide)
theorem original_id4522 : original4522.index = 4522 := by decide

def c4522 : Contract := original4522.toContract.get (by decide)
theorem binding4522 : original4522.toContract = some c4522 := rfl

theorem checked4522 : check 4000 c4522 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4523 : RawOriginal := C035.records[43]'(by decide)
theorem original_id4523 : original4523.index = 4523 := by decide

def c4523 : Contract := original4523.toContract.get (by decide)
theorem binding4523 : original4523.toContract = some c4523 := rfl

theorem checked4523 : check 4000 c4523 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4524 : RawOriginal := C035.records[44]'(by decide)
theorem original_id4524 : original4524.index = 4524 := by decide

def c4524 : Contract := original4524.toContract.get (by decide)
theorem binding4524 : original4524.toContract = some c4524 := rfl

theorem checked4524 : check 4000 c4524 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4525 : RawOriginal := C035.records[45]'(by decide)
theorem original_id4525 : original4525.index = 4525 := by decide

def c4525 : Contract := original4525.toContract.get (by decide)
theorem binding4525 : original4525.toContract = some c4525 := rfl

theorem checked4525 : check 4000 c4525 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4526 : RawOriginal := C035.records[46]'(by decide)
theorem original_id4526 : original4526.index = 4526 := by decide

def c4526 : Contract := original4526.toContract.get (by decide)
theorem binding4526 : original4526.toContract = some c4526 := rfl

theorem checked4526 : check 4000 c4526 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4527 : RawOriginal := C035.records[47]'(by decide)
theorem original_id4527 : original4527.index = 4527 := by decide

def c4527 : Contract := original4527.toContract.get (by decide)
theorem binding4527 : original4527.toContract = some c4527 := rfl

theorem checked4527 : check 4000 c4527 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4528 : RawOriginal := C035.records[48]'(by decide)
theorem original_id4528 : original4528.index = 4528 := by decide

def c4528 : Contract := original4528.toContract.get (by decide)
theorem binding4528 : original4528.toContract = some c4528 := rfl

theorem checked4528 : check 4000 c4528 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4529 : RawOriginal := C035.records[49]'(by decide)
theorem original_id4529 : original4529.index = 4529 := by decide

def c4529 : Contract := original4529.toContract.get (by decide)
theorem binding4529 : original4529.toContract = some c4529 := rfl

theorem checked4529 : check 4000 c4529 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4530 : RawOriginal := C035.records[50]'(by decide)
theorem original_id4530 : original4530.index = 4530 := by decide

def c4530 : Contract := original4530.toContract.get (by decide)
theorem binding4530 : original4530.toContract = some c4530 := rfl

theorem checked4530 : check 4000 c4530 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4531 : RawOriginal := C035.records[51]'(by decide)
theorem original_id4531 : original4531.index = 4531 := by decide

def c4531 : Contract := original4531.toContract.get (by decide)
theorem binding4531 : original4531.toContract = some c4531 := rfl

theorem checked4531 : check 4000 c4531 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4532 : RawOriginal := C035.records[52]'(by decide)
theorem original_id4532 : original4532.index = 4532 := by decide

def c4532 : Contract := original4532.toContract.get (by decide)
theorem binding4532 : original4532.toContract = some c4532 := rfl

theorem checked4532 : check 4000 c4532 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4533 : RawOriginal := C035.records[53]'(by decide)
theorem original_id4533 : original4533.index = 4533 := by decide

def c4533 : Contract := original4533.toContract.get (by decide)
theorem binding4533 : original4533.toContract = some c4533 := rfl

theorem checked4533 : check 4000 c4533 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4518, c4518, 4000, checked4518⟩,
  ⟨4519, c4519, 4000, checked4519⟩,
  ⟨4520, c4520, 4000, checked4520⟩,
  ⟨4521, c4521, 4000, checked4521⟩,
  ⟨4522, c4522, 4000, checked4522⟩,
  ⟨4523, c4523, 4000, checked4523⟩,
  ⟨4524, c4524, 4000, checked4524⟩,
  ⟨4525, c4525, 4000, checked4525⟩,
  ⟨4526, c4526, 4000, checked4526⟩,
  ⟨4527, c4527, 4000, checked4527⟩,
  ⟨4528, c4528, 4000, checked4528⟩,
  ⟨4529, c4529, 4000, checked4529⟩,
  ⟨4530, c4530, 4000, checked4530⟩,
  ⟨4531, c4531, 4000, checked4531⟩,
  ⟨4532, c4532, 4000, checked4532⟩,
  ⟨4533, c4533, 4000, checked4533⟩]

end PA215.ContractShards.Shard035Part2
