import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C020
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard020Part4
open PA215.Contracts PA215.Census

def original2630 : RawOriginal := C020.records[70]'(by decide)
theorem original_id2630 : original2630.index = 2630 := by decide

def c2630 : Contract := original2630.toContract.get (by decide)
theorem binding2630 : original2630.toContract = some c2630 := rfl

theorem checked2630 : check 4000 c2630 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2631 : RawOriginal := C020.records[71]'(by decide)
theorem original_id2631 : original2631.index = 2631 := by decide

def c2631 : Contract := original2631.toContract.get (by decide)
theorem binding2631 : original2631.toContract = some c2631 := rfl

theorem checked2631 : check 4000 c2631 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2632 : RawOriginal := C020.records[72]'(by decide)
theorem original_id2632 : original2632.index = 2632 := by decide

def c2632 : Contract := original2632.toContract.get (by decide)
theorem binding2632 : original2632.toContract = some c2632 := rfl

theorem checked2632 : check 4000 c2632 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2633 : RawOriginal := C020.records[73]'(by decide)
theorem original_id2633 : original2633.index = 2633 := by decide

def c2633 : Contract := original2633.toContract.get (by decide)
theorem binding2633 : original2633.toContract = some c2633 := rfl

theorem checked2633 : check 4000 c2633 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2634 : RawOriginal := C020.records[74]'(by decide)
theorem original_id2634 : original2634.index = 2634 := by decide

def c2634 : Contract := original2634.toContract.get (by decide)
theorem binding2634 : original2634.toContract = some c2634 := rfl

theorem checked2634 : check 4000 c2634 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2635 : RawOriginal := C020.records[75]'(by decide)
theorem original_id2635 : original2635.index = 2635 := by decide

def c2635 : Contract := original2635.toContract.get (by decide)
theorem binding2635 : original2635.toContract = some c2635 := rfl

theorem checked2635 : check 4000 c2635 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2636 : RawOriginal := C020.records[76]'(by decide)
theorem original_id2636 : original2636.index = 2636 := by decide

def c2636 : Contract := original2636.toContract.get (by decide)
theorem binding2636 : original2636.toContract = some c2636 := rfl

theorem checked2636 : check 4000 c2636 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2637 : RawOriginal := C020.records[77]'(by decide)
theorem original_id2637 : original2637.index = 2637 := by decide

def c2637 : Contract := original2637.toContract.get (by decide)
theorem binding2637 : original2637.toContract = some c2637 := rfl

theorem checked2637 : check 4000 c2637 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2638 : RawOriginal := C020.records[78]'(by decide)
theorem original_id2638 : original2638.index = 2638 := by decide

def c2638 : Contract := original2638.toContract.get (by decide)
theorem binding2638 : original2638.toContract = some c2638 := rfl

theorem checked2638 : check 4000 c2638 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2639 : RawOriginal := C020.records[79]'(by decide)
theorem original_id2639 : original2639.index = 2639 := by decide

def c2639 : Contract := original2639.toContract.get (by decide)
theorem binding2639 : original2639.toContract = some c2639 := rfl

theorem checked2639 : check 4000 c2639 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2640 : RawOriginal := C020.records[80]'(by decide)
theorem original_id2640 : original2640.index = 2640 := by decide

def c2640 : Contract := original2640.toContract.get (by decide)
theorem binding2640 : original2640.toContract = some c2640 := rfl

theorem checked2640 : check 4000 c2640 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2641 : RawOriginal := C020.records[81]'(by decide)
theorem original_id2641 : original2641.index = 2641 := by decide

def c2641 : Contract := original2641.toContract.get (by decide)
theorem binding2641 : original2641.toContract = some c2641 := rfl

theorem checked2641 : check 4000 c2641 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2642 : RawOriginal := C020.records[82]'(by decide)
theorem original_id2642 : original2642.index = 2642 := by decide

def c2642 : Contract := original2642.toContract.get (by decide)
theorem binding2642 : original2642.toContract = some c2642 := rfl

theorem checked2642 : check 4000 c2642 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2643 : RawOriginal := C020.records[83]'(by decide)
theorem original_id2643 : original2643.index = 2643 := by decide

def c2643 : Contract := original2643.toContract.get (by decide)
theorem binding2643 : original2643.toContract = some c2643 := rfl

theorem checked2643 : check 4000 c2643 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2644 : RawOriginal := C020.records[84]'(by decide)
theorem original_id2644 : original2644.index = 2644 := by decide

def c2644 : Contract := original2644.toContract.get (by decide)
theorem binding2644 : original2644.toContract = some c2644 := rfl

theorem checked2644 : check 4000 c2644 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2645 : RawOriginal := C020.records[85]'(by decide)
theorem original_id2645 : original2645.index = 2645 := by decide

def c2645 : Contract := original2645.toContract.get (by decide)
theorem binding2645 : original2645.toContract = some c2645 := rfl

theorem checked2645 : check 4000 c2645 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2630, c2630, 4000, checked2630⟩,
  ⟨2631, c2631, 4000, checked2631⟩,
  ⟨2632, c2632, 4000, checked2632⟩,
  ⟨2633, c2633, 4000, checked2633⟩,
  ⟨2634, c2634, 4000, checked2634⟩,
  ⟨2635, c2635, 4000, checked2635⟩,
  ⟨2636, c2636, 4000, checked2636⟩,
  ⟨2637, c2637, 4000, checked2637⟩,
  ⟨2638, c2638, 4000, checked2638⟩,
  ⟨2639, c2639, 4000, checked2639⟩,
  ⟨2640, c2640, 4000, checked2640⟩,
  ⟨2641, c2641, 4000, checked2641⟩,
  ⟨2642, c2642, 4000, checked2642⟩,
  ⟨2643, c2643, 4000, checked2643⟩,
  ⟨2644, c2644, 4000, checked2644⟩,
  ⟨2645, c2645, 4000, checked2645⟩]

end PA215.ContractShards.Shard020Part4
