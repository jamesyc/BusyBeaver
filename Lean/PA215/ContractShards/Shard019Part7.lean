import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C019
import PA215.Census.C020
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard019Part7
open PA215.Contracts PA215.Census

def original2550 : RawOriginal := C019.records[118]'(by decide)
theorem original_id2550 : original2550.index = 2550 := by decide

def c2550 : Contract := original2550.toContract.get (by decide)
theorem binding2550 : original2550.toContract = some c2550 := rfl

theorem checked2550 : check 4000 c2550 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2551 : RawOriginal := C019.records[119]'(by decide)
theorem original_id2551 : original2551.index = 2551 := by decide

def c2551 : Contract := original2551.toContract.get (by decide)
theorem binding2551 : original2551.toContract = some c2551 := rfl

theorem checked2551 : check 4000 c2551 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2552 : RawOriginal := C019.records[120]'(by decide)
theorem original_id2552 : original2552.index = 2552 := by decide

def c2552 : Contract := original2552.toContract.get (by decide)
theorem binding2552 : original2552.toContract = some c2552 := rfl

theorem checked2552 : check 4000 c2552 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2553 : RawOriginal := C019.records[121]'(by decide)
theorem original_id2553 : original2553.index = 2553 := by decide

def c2553 : Contract := original2553.toContract.get (by decide)
theorem binding2553 : original2553.toContract = some c2553 := rfl

theorem checked2553 : check 4000 c2553 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2554 : RawOriginal := C019.records[122]'(by decide)
theorem original_id2554 : original2554.index = 2554 := by decide

def c2554 : Contract := original2554.toContract.get (by decide)
theorem binding2554 : original2554.toContract = some c2554 := rfl

theorem checked2554 : check 4000 c2554 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2555 : RawOriginal := C019.records[123]'(by decide)
theorem original_id2555 : original2555.index = 2555 := by decide

def c2555 : Contract := original2555.toContract.get (by decide)
theorem binding2555 : original2555.toContract = some c2555 := rfl

theorem checked2555 : check 4000 c2555 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2556 : RawOriginal := C019.records[124]'(by decide)
theorem original_id2556 : original2556.index = 2556 := by decide

def c2556 : Contract := original2556.toContract.get (by decide)
theorem binding2556 : original2556.toContract = some c2556 := rfl

theorem checked2556 : check 4000 c2556 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2557 : RawOriginal := C019.records[125]'(by decide)
theorem original_id2557 : original2557.index = 2557 := by decide

def c2557 : Contract := original2557.toContract.get (by decide)
theorem binding2557 : original2557.toContract = some c2557 := rfl

theorem checked2557 : check 4000 c2557 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2558 : RawOriginal := C019.records[126]'(by decide)
theorem original_id2558 : original2558.index = 2558 := by decide

def c2558 : Contract := original2558.toContract.get (by decide)
theorem binding2558 : original2558.toContract = some c2558 := rfl

theorem checked2558 : check 4000 c2558 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2559 : RawOriginal := C019.records[127]'(by decide)
theorem original_id2559 : original2559.index = 2559 := by decide

def c2559 : Contract := original2559.toContract.get (by decide)
theorem binding2559 : original2559.toContract = some c2559 := rfl

theorem checked2559 : check 4000 c2559 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2560 : RawOriginal := C020.records[0]'(by decide)
theorem original_id2560 : original2560.index = 2560 := by decide

def c2560 : Contract := original2560.toContract.get (by decide)
theorem binding2560 : original2560.toContract = some c2560 := rfl

theorem checked2560 : check 4000 c2560 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2561 : RawOriginal := C020.records[1]'(by decide)
theorem original_id2561 : original2561.index = 2561 := by decide

def c2561 : Contract := original2561.toContract.get (by decide)
theorem binding2561 : original2561.toContract = some c2561 := rfl

theorem checked2561 : check 4000 c2561 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2562 : RawOriginal := C020.records[2]'(by decide)
theorem original_id2562 : original2562.index = 2562 := by decide

def c2562 : Contract := original2562.toContract.get (by decide)
theorem binding2562 : original2562.toContract = some c2562 := rfl

theorem checked2562 : check 4000 c2562 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2563 : RawOriginal := C020.records[3]'(by decide)
theorem original_id2563 : original2563.index = 2563 := by decide

def c2563 : Contract := original2563.toContract.get (by decide)
theorem binding2563 : original2563.toContract = some c2563 := rfl

theorem checked2563 : check 4000 c2563 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2564 : RawOriginal := C020.records[4]'(by decide)
theorem original_id2564 : original2564.index = 2564 := by decide

def c2564 : Contract := original2564.toContract.get (by decide)
theorem binding2564 : original2564.toContract = some c2564 := rfl

theorem checked2564 : check 4000 c2564 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2565 : RawOriginal := C020.records[5]'(by decide)
theorem original_id2565 : original2565.index = 2565 := by decide

def c2565 : Contract := original2565.toContract.get (by decide)
theorem binding2565 : original2565.toContract = some c2565 := rfl

theorem checked2565 : check 4000 c2565 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2550, c2550, 4000, checked2550⟩,
  ⟨2551, c2551, 4000, checked2551⟩,
  ⟨2552, c2552, 4000, checked2552⟩,
  ⟨2553, c2553, 4000, checked2553⟩,
  ⟨2554, c2554, 4000, checked2554⟩,
  ⟨2555, c2555, 4000, checked2555⟩,
  ⟨2556, c2556, 4000, checked2556⟩,
  ⟨2557, c2557, 4000, checked2557⟩,
  ⟨2558, c2558, 4000, checked2558⟩,
  ⟨2559, c2559, 4000, checked2559⟩,
  ⟨2560, c2560, 4000, checked2560⟩,
  ⟨2561, c2561, 4000, checked2561⟩,
  ⟨2562, c2562, 4000, checked2562⟩,
  ⟨2563, c2563, 4000, checked2563⟩,
  ⟨2564, c2564, 4000, checked2564⟩,
  ⟨2565, c2565, 4000, checked2565⟩]

end PA215.ContractShards.Shard019Part7
