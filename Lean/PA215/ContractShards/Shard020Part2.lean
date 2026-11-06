import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C020
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard020Part2
open PA215.Contracts PA215.Census

def original2598 : RawOriginal := C020.records[38]'(by decide)
theorem original_id2598 : original2598.index = 2598 := by decide

def c2598 : Contract := original2598.toContract.get (by decide)
theorem binding2598 : original2598.toContract = some c2598 := rfl

theorem checked2598 : check 4000 c2598 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2599 : RawOriginal := C020.records[39]'(by decide)
theorem original_id2599 : original2599.index = 2599 := by decide

def c2599 : Contract := original2599.toContract.get (by decide)
theorem binding2599 : original2599.toContract = some c2599 := rfl

theorem checked2599 : check 4000 c2599 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2600 : RawOriginal := C020.records[40]'(by decide)
theorem original_id2600 : original2600.index = 2600 := by decide

def c2600 : Contract := original2600.toContract.get (by decide)
theorem binding2600 : original2600.toContract = some c2600 := rfl

theorem checked2600 : check 4000 c2600 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2601 : RawOriginal := C020.records[41]'(by decide)
theorem original_id2601 : original2601.index = 2601 := by decide

def c2601 : Contract := original2601.toContract.get (by decide)
theorem binding2601 : original2601.toContract = some c2601 := rfl

theorem checked2601 : check 4000 c2601 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2602 : RawOriginal := C020.records[42]'(by decide)
theorem original_id2602 : original2602.index = 2602 := by decide

def c2602 : Contract := original2602.toContract.get (by decide)
theorem binding2602 : original2602.toContract = some c2602 := rfl

theorem checked2602 : check 4000 c2602 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2603 : RawOriginal := C020.records[43]'(by decide)
theorem original_id2603 : original2603.index = 2603 := by decide

def c2603 : Contract := original2603.toContract.get (by decide)
theorem binding2603 : original2603.toContract = some c2603 := rfl

theorem checked2603 : check 4000 c2603 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2604 : RawOriginal := C020.records[44]'(by decide)
theorem original_id2604 : original2604.index = 2604 := by decide

def c2604 : Contract := original2604.toContract.get (by decide)
theorem binding2604 : original2604.toContract = some c2604 := rfl

theorem checked2604 : check 4000 c2604 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2605 : RawOriginal := C020.records[45]'(by decide)
theorem original_id2605 : original2605.index = 2605 := by decide

def c2605 : Contract := original2605.toContract.get (by decide)
theorem binding2605 : original2605.toContract = some c2605 := rfl

theorem checked2605 : check 4000 c2605 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2606 : RawOriginal := C020.records[46]'(by decide)
theorem original_id2606 : original2606.index = 2606 := by decide

def c2606 : Contract := original2606.toContract.get (by decide)
theorem binding2606 : original2606.toContract = some c2606 := rfl

theorem checked2606 : check 4000 c2606 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2607 : RawOriginal := C020.records[47]'(by decide)
theorem original_id2607 : original2607.index = 2607 := by decide

def c2607 : Contract := original2607.toContract.get (by decide)
theorem binding2607 : original2607.toContract = some c2607 := rfl

theorem checked2607 : check 4000 c2607 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2608 : RawOriginal := C020.records[48]'(by decide)
theorem original_id2608 : original2608.index = 2608 := by decide

def c2608 : Contract := original2608.toContract.get (by decide)
theorem binding2608 : original2608.toContract = some c2608 := rfl

theorem checked2608 : check 4000 c2608 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2609 : RawOriginal := C020.records[49]'(by decide)
theorem original_id2609 : original2609.index = 2609 := by decide

def c2609 : Contract := original2609.toContract.get (by decide)
theorem binding2609 : original2609.toContract = some c2609 := rfl

theorem checked2609 : check 4000 c2609 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2610 : RawOriginal := C020.records[50]'(by decide)
theorem original_id2610 : original2610.index = 2610 := by decide

def c2610 : Contract := original2610.toContract.get (by decide)
theorem binding2610 : original2610.toContract = some c2610 := rfl

theorem checked2610 : check 4000 c2610 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2611 : RawOriginal := C020.records[51]'(by decide)
theorem original_id2611 : original2611.index = 2611 := by decide

def c2611 : Contract := original2611.toContract.get (by decide)
theorem binding2611 : original2611.toContract = some c2611 := rfl

theorem checked2611 : check 4000 c2611 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2612 : RawOriginal := C020.records[52]'(by decide)
theorem original_id2612 : original2612.index = 2612 := by decide

def c2612 : Contract := original2612.toContract.get (by decide)
theorem binding2612 : original2612.toContract = some c2612 := rfl

theorem checked2612 : check 4000 c2612 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2613 : RawOriginal := C020.records[53]'(by decide)
theorem original_id2613 : original2613.index = 2613 := by decide

def c2613 : Contract := original2613.toContract.get (by decide)
theorem binding2613 : original2613.toContract = some c2613 := rfl

theorem checked2613 : check 4000 c2613 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2598, c2598, 4000, checked2598⟩,
  ⟨2599, c2599, 4000, checked2599⟩,
  ⟨2600, c2600, 4000, checked2600⟩,
  ⟨2601, c2601, 4000, checked2601⟩,
  ⟨2602, c2602, 4000, checked2602⟩,
  ⟨2603, c2603, 4000, checked2603⟩,
  ⟨2604, c2604, 4000, checked2604⟩,
  ⟨2605, c2605, 4000, checked2605⟩,
  ⟨2606, c2606, 4000, checked2606⟩,
  ⟨2607, c2607, 4000, checked2607⟩,
  ⟨2608, c2608, 4000, checked2608⟩,
  ⟨2609, c2609, 4000, checked2609⟩,
  ⟨2610, c2610, 4000, checked2610⟩,
  ⟨2611, c2611, 4000, checked2611⟩,
  ⟨2612, c2612, 4000, checked2612⟩,
  ⟨2613, c2613, 4000, checked2613⟩]

end PA215.ContractShards.Shard020Part2
