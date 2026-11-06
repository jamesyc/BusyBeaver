import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C035
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard035Part4
open PA215.Contracts PA215.Census

def original4550 : RawOriginal := C035.records[70]'(by decide)
theorem original_id4550 : original4550.index = 4550 := by decide

def c4550 : Contract := original4550.toContract.get (by decide)
theorem binding4550 : original4550.toContract = some c4550 := rfl

theorem checked4550 : check 4000 c4550 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4551 : RawOriginal := C035.records[71]'(by decide)
theorem original_id4551 : original4551.index = 4551 := by decide

def c4551 : Contract := original4551.toContract.get (by decide)
theorem binding4551 : original4551.toContract = some c4551 := rfl

theorem checked4551 : check 4000 c4551 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4552 : RawOriginal := C035.records[72]'(by decide)
theorem original_id4552 : original4552.index = 4552 := by decide

def c4552 : Contract := original4552.toContract.get (by decide)
theorem binding4552 : original4552.toContract = some c4552 := rfl

theorem checked4552 : check 4000 c4552 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4553 : RawOriginal := C035.records[73]'(by decide)
theorem original_id4553 : original4553.index = 4553 := by decide

def c4553 : Contract := original4553.toContract.get (by decide)
theorem binding4553 : original4553.toContract = some c4553 := rfl

theorem checked4553 : check 4000 c4553 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4554 : RawOriginal := C035.records[74]'(by decide)
theorem original_id4554 : original4554.index = 4554 := by decide

def c4554 : Contract := original4554.toContract.get (by decide)
theorem binding4554 : original4554.toContract = some c4554 := rfl

theorem checked4554 : check 4000 c4554 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4555 : RawOriginal := C035.records[75]'(by decide)
theorem original_id4555 : original4555.index = 4555 := by decide

def c4555 : Contract := original4555.toContract.get (by decide)
theorem binding4555 : original4555.toContract = some c4555 := rfl

theorem checked4555 : check 4000 c4555 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4556 : RawOriginal := C035.records[76]'(by decide)
theorem original_id4556 : original4556.index = 4556 := by decide

def c4556 : Contract := original4556.toContract.get (by decide)
theorem binding4556 : original4556.toContract = some c4556 := rfl

theorem checked4556 : check 4000 c4556 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4557 : RawOriginal := C035.records[77]'(by decide)
theorem original_id4557 : original4557.index = 4557 := by decide

def c4557 : Contract := original4557.toContract.get (by decide)
theorem binding4557 : original4557.toContract = some c4557 := rfl

theorem checked4557 : check 4000 c4557 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4558 : RawOriginal := C035.records[78]'(by decide)
theorem original_id4558 : original4558.index = 4558 := by decide

def c4558 : Contract := original4558.toContract.get (by decide)
theorem binding4558 : original4558.toContract = some c4558 := rfl

theorem checked4558 : check 4000 c4558 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4559 : RawOriginal := C035.records[79]'(by decide)
theorem original_id4559 : original4559.index = 4559 := by decide

def c4559 : Contract := original4559.toContract.get (by decide)
theorem binding4559 : original4559.toContract = some c4559 := rfl

theorem checked4559 : check 4000 c4559 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4560 : RawOriginal := C035.records[80]'(by decide)
theorem original_id4560 : original4560.index = 4560 := by decide

def c4560 : Contract := original4560.toContract.get (by decide)
theorem binding4560 : original4560.toContract = some c4560 := rfl

theorem checked4560 : check 4000 c4560 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4561 : RawOriginal := C035.records[81]'(by decide)
theorem original_id4561 : original4561.index = 4561 := by decide

def c4561 : Contract := original4561.toContract.get (by decide)
theorem binding4561 : original4561.toContract = some c4561 := rfl

theorem checked4561 : check 4000 c4561 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4562 : RawOriginal := C035.records[82]'(by decide)
theorem original_id4562 : original4562.index = 4562 := by decide

def c4562 : Contract := original4562.toContract.get (by decide)
theorem binding4562 : original4562.toContract = some c4562 := rfl

theorem checked4562 : check 4000 c4562 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4563 : RawOriginal := C035.records[83]'(by decide)
theorem original_id4563 : original4563.index = 4563 := by decide

def c4563 : Contract := original4563.toContract.get (by decide)
theorem binding4563 : original4563.toContract = some c4563 := rfl

theorem checked4563 : check 4000 c4563 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4564 : RawOriginal := C035.records[84]'(by decide)
theorem original_id4564 : original4564.index = 4564 := by decide

def c4564 : Contract := original4564.toContract.get (by decide)
theorem binding4564 : original4564.toContract = some c4564 := rfl

theorem checked4564 : check 4000 c4564 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4565 : RawOriginal := C035.records[85]'(by decide)
theorem original_id4565 : original4565.index = 4565 := by decide

def c4565 : Contract := original4565.toContract.get (by decide)
theorem binding4565 : original4565.toContract = some c4565 := rfl

theorem checked4565 : check 4000 c4565 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4550, c4550, 4000, checked4550⟩,
  ⟨4551, c4551, 4000, checked4551⟩,
  ⟨4552, c4552, 4000, checked4552⟩,
  ⟨4553, c4553, 4000, checked4553⟩,
  ⟨4554, c4554, 4000, checked4554⟩,
  ⟨4555, c4555, 4000, checked4555⟩,
  ⟨4556, c4556, 4000, checked4556⟩,
  ⟨4557, c4557, 4000, checked4557⟩,
  ⟨4558, c4558, 4000, checked4558⟩,
  ⟨4559, c4559, 4000, checked4559⟩,
  ⟨4560, c4560, 4000, checked4560⟩,
  ⟨4561, c4561, 4000, checked4561⟩,
  ⟨4562, c4562, 4000, checked4562⟩,
  ⟨4563, c4563, 4000, checked4563⟩,
  ⟨4564, c4564, 4000, checked4564⟩,
  ⟨4565, c4565, 4000, checked4565⟩]

end PA215.ContractShards.Shard035Part4
