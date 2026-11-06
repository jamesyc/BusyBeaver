import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C035
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard035Part0
open PA215.Contracts PA215.Census

def original4486 : RawOriginal := C035.records[6]'(by decide)
theorem original_id4486 : original4486.index = 4486 := by decide

def c4486 : Contract := original4486.toContract.get (by decide)
theorem binding4486 : original4486.toContract = some c4486 := rfl

theorem checked4486 : check 4000 c4486 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4487 : RawOriginal := C035.records[7]'(by decide)
theorem original_id4487 : original4487.index = 4487 := by decide

def c4487 : Contract := original4487.toContract.get (by decide)
theorem binding4487 : original4487.toContract = some c4487 := rfl

theorem checked4487 : check 4000 c4487 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4488 : RawOriginal := C035.records[8]'(by decide)
theorem original_id4488 : original4488.index = 4488 := by decide

def c4488 : Contract := original4488.toContract.get (by decide)
theorem binding4488 : original4488.toContract = some c4488 := rfl

theorem checked4488 : check 4000 c4488 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4489 : RawOriginal := C035.records[9]'(by decide)
theorem original_id4489 : original4489.index = 4489 := by decide

def c4489 : Contract := original4489.toContract.get (by decide)
theorem binding4489 : original4489.toContract = some c4489 := rfl

theorem checked4489 : check 4000 c4489 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4490 : RawOriginal := C035.records[10]'(by decide)
theorem original_id4490 : original4490.index = 4490 := by decide

def c4490 : Contract := original4490.toContract.get (by decide)
theorem binding4490 : original4490.toContract = some c4490 := rfl

theorem checked4490 : check 4000 c4490 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4491 : RawOriginal := C035.records[11]'(by decide)
theorem original_id4491 : original4491.index = 4491 := by decide

def c4491 : Contract := original4491.toContract.get (by decide)
theorem binding4491 : original4491.toContract = some c4491 := rfl

theorem checked4491 : check 4000 c4491 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4492 : RawOriginal := C035.records[12]'(by decide)
theorem original_id4492 : original4492.index = 4492 := by decide

def c4492 : Contract := original4492.toContract.get (by decide)
theorem binding4492 : original4492.toContract = some c4492 := rfl

theorem checked4492 : check 4000 c4492 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4493 : RawOriginal := C035.records[13]'(by decide)
theorem original_id4493 : original4493.index = 4493 := by decide

def c4493 : Contract := original4493.toContract.get (by decide)
theorem binding4493 : original4493.toContract = some c4493 := rfl

theorem checked4493 : check 4000 c4493 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4494 : RawOriginal := C035.records[14]'(by decide)
theorem original_id4494 : original4494.index = 4494 := by decide

def c4494 : Contract := original4494.toContract.get (by decide)
theorem binding4494 : original4494.toContract = some c4494 := rfl

theorem checked4494 : check 4000 c4494 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4495 : RawOriginal := C035.records[15]'(by decide)
theorem original_id4495 : original4495.index = 4495 := by decide

def c4495 : Contract := original4495.toContract.get (by decide)
theorem binding4495 : original4495.toContract = some c4495 := rfl

theorem checked4495 : check 4000 c4495 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4496 : RawOriginal := C035.records[16]'(by decide)
theorem original_id4496 : original4496.index = 4496 := by decide

def c4496 : Contract := original4496.toContract.get (by decide)
theorem binding4496 : original4496.toContract = some c4496 := rfl

theorem checked4496 : check 4000 c4496 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4497 : RawOriginal := C035.records[17]'(by decide)
theorem original_id4497 : original4497.index = 4497 := by decide

def c4497 : Contract := original4497.toContract.get (by decide)
theorem binding4497 : original4497.toContract = some c4497 := rfl

theorem checked4497 : check 4000 c4497 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4498 : RawOriginal := C035.records[18]'(by decide)
theorem original_id4498 : original4498.index = 4498 := by decide

def c4498 : Contract := original4498.toContract.get (by decide)
theorem binding4498 : original4498.toContract = some c4498 := rfl

theorem checked4498 : check 4000 c4498 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4499 : RawOriginal := C035.records[19]'(by decide)
theorem original_id4499 : original4499.index = 4499 := by decide

def c4499 : Contract := original4499.toContract.get (by decide)
theorem binding4499 : original4499.toContract = some c4499 := rfl

theorem checked4499 : check 4000 c4499 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4500 : RawOriginal := C035.records[20]'(by decide)
theorem original_id4500 : original4500.index = 4500 := by decide

def c4500 : Contract := original4500.toContract.get (by decide)
theorem binding4500 : original4500.toContract = some c4500 := rfl

theorem checked4500 : check 4000 c4500 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4501 : RawOriginal := C035.records[21]'(by decide)
theorem original_id4501 : original4501.index = 4501 := by decide

def c4501 : Contract := original4501.toContract.get (by decide)
theorem binding4501 : original4501.toContract = some c4501 := rfl

theorem checked4501 : check 4000 c4501 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4486, c4486, 4000, checked4486⟩,
  ⟨4487, c4487, 4000, checked4487⟩,
  ⟨4488, c4488, 4000, checked4488⟩,
  ⟨4489, c4489, 4000, checked4489⟩,
  ⟨4490, c4490, 4000, checked4490⟩,
  ⟨4491, c4491, 4000, checked4491⟩,
  ⟨4492, c4492, 4000, checked4492⟩,
  ⟨4493, c4493, 4000, checked4493⟩,
  ⟨4494, c4494, 4000, checked4494⟩,
  ⟨4495, c4495, 4000, checked4495⟩,
  ⟨4496, c4496, 4000, checked4496⟩,
  ⟨4497, c4497, 4000, checked4497⟩,
  ⟨4498, c4498, 4000, checked4498⟩,
  ⟨4499, c4499, 4000, checked4499⟩,
  ⟨4500, c4500, 4000, checked4500⟩,
  ⟨4501, c4501, 4000, checked4501⟩]

end PA215.ContractShards.Shard035Part0
