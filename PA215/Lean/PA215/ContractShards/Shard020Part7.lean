import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C020
import PA215.Census.C021
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard020Part7
open PA215.Contracts PA215.Census

def original2678 : RawOriginal := C020.records[118]'(by decide)
theorem original_id2678 : original2678.index = 2678 := by decide

def c2678 : Contract := original2678.toContract.get (by decide)
theorem binding2678 : original2678.toContract = some c2678 := rfl

theorem checked2678 : check 4000 c2678 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2679 : RawOriginal := C020.records[119]'(by decide)
theorem original_id2679 : original2679.index = 2679 := by decide

def c2679 : Contract := original2679.toContract.get (by decide)
theorem binding2679 : original2679.toContract = some c2679 := rfl

theorem checked2679 : check 4000 c2679 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2680 : RawOriginal := C020.records[120]'(by decide)
theorem original_id2680 : original2680.index = 2680 := by decide

def c2680 : Contract := original2680.toContract.get (by decide)
theorem binding2680 : original2680.toContract = some c2680 := rfl

theorem checked2680 : check 4000 c2680 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2681 : RawOriginal := C020.records[121]'(by decide)
theorem original_id2681 : original2681.index = 2681 := by decide

def c2681 : Contract := original2681.toContract.get (by decide)
theorem binding2681 : original2681.toContract = some c2681 := rfl

theorem checked2681 : check 4000 c2681 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2682 : RawOriginal := C020.records[122]'(by decide)
theorem original_id2682 : original2682.index = 2682 := by decide

def c2682 : Contract := original2682.toContract.get (by decide)
theorem binding2682 : original2682.toContract = some c2682 := rfl

theorem checked2682 : check 4000 c2682 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2683 : RawOriginal := C020.records[123]'(by decide)
theorem original_id2683 : original2683.index = 2683 := by decide

def c2683 : Contract := original2683.toContract.get (by decide)
theorem binding2683 : original2683.toContract = some c2683 := rfl

theorem checked2683 : check 4000 c2683 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2684 : RawOriginal := C020.records[124]'(by decide)
theorem original_id2684 : original2684.index = 2684 := by decide

def c2684 : Contract := original2684.toContract.get (by decide)
theorem binding2684 : original2684.toContract = some c2684 := rfl

theorem checked2684 : check 4000 c2684 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2685 : RawOriginal := C020.records[125]'(by decide)
theorem original_id2685 : original2685.index = 2685 := by decide

def c2685 : Contract := original2685.toContract.get (by decide)
theorem binding2685 : original2685.toContract = some c2685 := rfl

theorem checked2685 : check 4000 c2685 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2686 : RawOriginal := C020.records[126]'(by decide)
theorem original_id2686 : original2686.index = 2686 := by decide

def c2686 : Contract := original2686.toContract.get (by decide)
theorem binding2686 : original2686.toContract = some c2686 := rfl

theorem checked2686 : check 4000 c2686 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2687 : RawOriginal := C020.records[127]'(by decide)
theorem original_id2687 : original2687.index = 2687 := by decide

def c2687 : Contract := original2687.toContract.get (by decide)
theorem binding2687 : original2687.toContract = some c2687 := rfl

theorem checked2687 : check 4000 c2687 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2688 : RawOriginal := C021.records[0]'(by decide)
theorem original_id2688 : original2688.index = 2688 := by decide

def c2688 : Contract := original2688.toContract.get (by decide)
theorem binding2688 : original2688.toContract = some c2688 := rfl

theorem checked2688 : check 4000 c2688 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2689 : RawOriginal := C021.records[1]'(by decide)
theorem original_id2689 : original2689.index = 2689 := by decide

def c2689 : Contract := original2689.toContract.get (by decide)
theorem binding2689 : original2689.toContract = some c2689 := rfl

theorem checked2689 : check 4000 c2689 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2690 : RawOriginal := C021.records[2]'(by decide)
theorem original_id2690 : original2690.index = 2690 := by decide

def c2690 : Contract := original2690.toContract.get (by decide)
theorem binding2690 : original2690.toContract = some c2690 := rfl

theorem checked2690 : check 4000 c2690 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2691 : RawOriginal := C021.records[3]'(by decide)
theorem original_id2691 : original2691.index = 2691 := by decide

def c2691 : Contract := original2691.toContract.get (by decide)
theorem binding2691 : original2691.toContract = some c2691 := rfl

theorem checked2691 : check 4000 c2691 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2692 : RawOriginal := C021.records[4]'(by decide)
theorem original_id2692 : original2692.index = 2692 := by decide

def c2692 : Contract := original2692.toContract.get (by decide)
theorem binding2692 : original2692.toContract = some c2692 := rfl

theorem checked2692 : check 4000 c2692 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2693 : RawOriginal := C021.records[5]'(by decide)
theorem original_id2693 : original2693.index = 2693 := by decide

def c2693 : Contract := original2693.toContract.get (by decide)
theorem binding2693 : original2693.toContract = some c2693 := rfl

theorem checked2693 : check 4000 c2693 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2678, c2678, 4000, checked2678⟩,
  ⟨2679, c2679, 4000, checked2679⟩,
  ⟨2680, c2680, 4000, checked2680⟩,
  ⟨2681, c2681, 4000, checked2681⟩,
  ⟨2682, c2682, 4000, checked2682⟩,
  ⟨2683, c2683, 4000, checked2683⟩,
  ⟨2684, c2684, 4000, checked2684⟩,
  ⟨2685, c2685, 4000, checked2685⟩,
  ⟨2686, c2686, 4000, checked2686⟩,
  ⟨2687, c2687, 4000, checked2687⟩,
  ⟨2688, c2688, 4000, checked2688⟩,
  ⟨2689, c2689, 4000, checked2689⟩,
  ⟨2690, c2690, 4000, checked2690⟩,
  ⟨2691, c2691, 4000, checked2691⟩,
  ⟨2692, c2692, 4000, checked2692⟩,
  ⟨2693, c2693, 4000, checked2693⟩]

end PA215.ContractShards.Shard020Part7
