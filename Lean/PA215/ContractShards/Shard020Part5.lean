import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C020
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard020Part5
open PA215.Contracts PA215.Census

def original2646 : RawOriginal := C020.records[86]'(by decide)
theorem original_id2646 : original2646.index = 2646 := by decide

def c2646 : Contract := original2646.toContract.get (by decide)
theorem binding2646 : original2646.toContract = some c2646 := rfl

theorem checked2646 : check 4000 c2646 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2647 : RawOriginal := C020.records[87]'(by decide)
theorem original_id2647 : original2647.index = 2647 := by decide

def c2647 : Contract := original2647.toContract.get (by decide)
theorem binding2647 : original2647.toContract = some c2647 := rfl

theorem checked2647 : check 4000 c2647 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2648 : RawOriginal := C020.records[88]'(by decide)
theorem original_id2648 : original2648.index = 2648 := by decide

def c2648 : Contract := original2648.toContract.get (by decide)
theorem binding2648 : original2648.toContract = some c2648 := rfl

theorem checked2648 : check 4000 c2648 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2649 : RawOriginal := C020.records[89]'(by decide)
theorem original_id2649 : original2649.index = 2649 := by decide

def c2649 : Contract := original2649.toContract.get (by decide)
theorem binding2649 : original2649.toContract = some c2649 := rfl

theorem checked2649 : check 4000 c2649 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2650 : RawOriginal := C020.records[90]'(by decide)
theorem original_id2650 : original2650.index = 2650 := by decide

def c2650 : Contract := original2650.toContract.get (by decide)
theorem binding2650 : original2650.toContract = some c2650 := rfl

theorem checked2650 : check 4000 c2650 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2651 : RawOriginal := C020.records[91]'(by decide)
theorem original_id2651 : original2651.index = 2651 := by decide

def c2651 : Contract := original2651.toContract.get (by decide)
theorem binding2651 : original2651.toContract = some c2651 := rfl

theorem checked2651 : check 4000 c2651 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2652 : RawOriginal := C020.records[92]'(by decide)
theorem original_id2652 : original2652.index = 2652 := by decide

def c2652 : Contract := original2652.toContract.get (by decide)
theorem binding2652 : original2652.toContract = some c2652 := rfl

theorem checked2652 : check 4000 c2652 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2653 : RawOriginal := C020.records[93]'(by decide)
theorem original_id2653 : original2653.index = 2653 := by decide

def c2653 : Contract := original2653.toContract.get (by decide)
theorem binding2653 : original2653.toContract = some c2653 := rfl

theorem checked2653 : check 4000 c2653 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2654 : RawOriginal := C020.records[94]'(by decide)
theorem original_id2654 : original2654.index = 2654 := by decide

def c2654 : Contract := original2654.toContract.get (by decide)
theorem binding2654 : original2654.toContract = some c2654 := rfl

theorem checked2654 : check 4000 c2654 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2655 : RawOriginal := C020.records[95]'(by decide)
theorem original_id2655 : original2655.index = 2655 := by decide

def c2655 : Contract := original2655.toContract.get (by decide)
theorem binding2655 : original2655.toContract = some c2655 := rfl

theorem checked2655 : check 4000 c2655 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2656 : RawOriginal := C020.records[96]'(by decide)
theorem original_id2656 : original2656.index = 2656 := by decide

def c2656 : Contract := original2656.toContract.get (by decide)
theorem binding2656 : original2656.toContract = some c2656 := rfl

theorem checked2656 : check 4000 c2656 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2657 : RawOriginal := C020.records[97]'(by decide)
theorem original_id2657 : original2657.index = 2657 := by decide

def c2657 : Contract := original2657.toContract.get (by decide)
theorem binding2657 : original2657.toContract = some c2657 := rfl

theorem checked2657 : check 4000 c2657 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2658 : RawOriginal := C020.records[98]'(by decide)
theorem original_id2658 : original2658.index = 2658 := by decide

def c2658 : Contract := original2658.toContract.get (by decide)
theorem binding2658 : original2658.toContract = some c2658 := rfl

theorem checked2658 : check 4000 c2658 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2659 : RawOriginal := C020.records[99]'(by decide)
theorem original_id2659 : original2659.index = 2659 := by decide

def c2659 : Contract := original2659.toContract.get (by decide)
theorem binding2659 : original2659.toContract = some c2659 := rfl

theorem checked2659 : check 4000 c2659 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2660 : RawOriginal := C020.records[100]'(by decide)
theorem original_id2660 : original2660.index = 2660 := by decide

def c2660 : Contract := original2660.toContract.get (by decide)
theorem binding2660 : original2660.toContract = some c2660 := rfl

theorem checked2660 : check 4000 c2660 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2661 : RawOriginal := C020.records[101]'(by decide)
theorem original_id2661 : original2661.index = 2661 := by decide

def c2661 : Contract := original2661.toContract.get (by decide)
theorem binding2661 : original2661.toContract = some c2661 := rfl

theorem checked2661 : check 4000 c2661 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2646, c2646, 4000, checked2646⟩,
  ⟨2647, c2647, 4000, checked2647⟩,
  ⟨2648, c2648, 4000, checked2648⟩,
  ⟨2649, c2649, 4000, checked2649⟩,
  ⟨2650, c2650, 4000, checked2650⟩,
  ⟨2651, c2651, 4000, checked2651⟩,
  ⟨2652, c2652, 4000, checked2652⟩,
  ⟨2653, c2653, 4000, checked2653⟩,
  ⟨2654, c2654, 4000, checked2654⟩,
  ⟨2655, c2655, 4000, checked2655⟩,
  ⟨2656, c2656, 4000, checked2656⟩,
  ⟨2657, c2657, 4000, checked2657⟩,
  ⟨2658, c2658, 4000, checked2658⟩,
  ⟨2659, c2659, 4000, checked2659⟩,
  ⟨2660, c2660, 4000, checked2660⟩,
  ⟨2661, c2661, 4000, checked2661⟩]

end PA215.ContractShards.Shard020Part5
