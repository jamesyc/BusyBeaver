import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C021
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard021Part6
open PA215.Contracts PA215.Census

def original2790 : RawOriginal := C021.records[102]'(by decide)
theorem original_id2790 : original2790.index = 2790 := by decide

def c2790 : Contract := original2790.toContract.get (by decide)
theorem binding2790 : original2790.toContract = some c2790 := rfl

theorem checked2790 : check 4000 c2790 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2791 : RawOriginal := C021.records[103]'(by decide)
theorem original_id2791 : original2791.index = 2791 := by decide

def c2791 : Contract := original2791.toContract.get (by decide)
theorem binding2791 : original2791.toContract = some c2791 := rfl

theorem checked2791 : check 4000 c2791 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2792 : RawOriginal := C021.records[104]'(by decide)
theorem original_id2792 : original2792.index = 2792 := by decide

def c2792 : Contract := original2792.toContract.get (by decide)
theorem binding2792 : original2792.toContract = some c2792 := rfl

theorem checked2792 : check 4000 c2792 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2793 : RawOriginal := C021.records[105]'(by decide)
theorem original_id2793 : original2793.index = 2793 := by decide

def c2793 : Contract := original2793.toContract.get (by decide)
theorem binding2793 : original2793.toContract = some c2793 := rfl

theorem checked2793 : check 4000 c2793 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2794 : RawOriginal := C021.records[106]'(by decide)
theorem original_id2794 : original2794.index = 2794 := by decide

def c2794 : Contract := original2794.toContract.get (by decide)
theorem binding2794 : original2794.toContract = some c2794 := rfl

theorem checked2794 : check 4000 c2794 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2795 : RawOriginal := C021.records[107]'(by decide)
theorem original_id2795 : original2795.index = 2795 := by decide

def c2795 : Contract := original2795.toContract.get (by decide)
theorem binding2795 : original2795.toContract = some c2795 := rfl

theorem checked2795 : check 4000 c2795 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2796 : RawOriginal := C021.records[108]'(by decide)
theorem original_id2796 : original2796.index = 2796 := by decide

def c2796 : Contract := original2796.toContract.get (by decide)
theorem binding2796 : original2796.toContract = some c2796 := rfl

theorem checked2796 : check 4000 c2796 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2797 : RawOriginal := C021.records[109]'(by decide)
theorem original_id2797 : original2797.index = 2797 := by decide

def c2797 : Contract := original2797.toContract.get (by decide)
theorem binding2797 : original2797.toContract = some c2797 := rfl

theorem checked2797 : check 4000 c2797 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2798 : RawOriginal := C021.records[110]'(by decide)
theorem original_id2798 : original2798.index = 2798 := by decide

def c2798 : Contract := original2798.toContract.get (by decide)
theorem binding2798 : original2798.toContract = some c2798 := rfl

theorem checked2798 : check 4000 c2798 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2799 : RawOriginal := C021.records[111]'(by decide)
theorem original_id2799 : original2799.index = 2799 := by decide

def c2799 : Contract := original2799.toContract.get (by decide)
theorem binding2799 : original2799.toContract = some c2799 := rfl

theorem checked2799 : check 4000 c2799 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2800 : RawOriginal := C021.records[112]'(by decide)
theorem original_id2800 : original2800.index = 2800 := by decide

def c2800 : Contract := original2800.toContract.get (by decide)
theorem binding2800 : original2800.toContract = some c2800 := rfl

theorem checked2800 : check 4000 c2800 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2801 : RawOriginal := C021.records[113]'(by decide)
theorem original_id2801 : original2801.index = 2801 := by decide

def c2801 : Contract := original2801.toContract.get (by decide)
theorem binding2801 : original2801.toContract = some c2801 := rfl

theorem checked2801 : check 4000 c2801 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2802 : RawOriginal := C021.records[114]'(by decide)
theorem original_id2802 : original2802.index = 2802 := by decide

def c2802 : Contract := original2802.toContract.get (by decide)
theorem binding2802 : original2802.toContract = some c2802 := rfl

theorem checked2802 : check 4000 c2802 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2803 : RawOriginal := C021.records[115]'(by decide)
theorem original_id2803 : original2803.index = 2803 := by decide

def c2803 : Contract := original2803.toContract.get (by decide)
theorem binding2803 : original2803.toContract = some c2803 := rfl

theorem checked2803 : check 4000 c2803 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2804 : RawOriginal := C021.records[116]'(by decide)
theorem original_id2804 : original2804.index = 2804 := by decide

def c2804 : Contract := original2804.toContract.get (by decide)
theorem binding2804 : original2804.toContract = some c2804 := rfl

theorem checked2804 : check 4000 c2804 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2805 : RawOriginal := C021.records[117]'(by decide)
theorem original_id2805 : original2805.index = 2805 := by decide

def c2805 : Contract := original2805.toContract.get (by decide)
theorem binding2805 : original2805.toContract = some c2805 := rfl

theorem checked2805 : check 4000 c2805 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2790, c2790, 4000, checked2790⟩,
  ⟨2791, c2791, 4000, checked2791⟩,
  ⟨2792, c2792, 4000, checked2792⟩,
  ⟨2793, c2793, 4000, checked2793⟩,
  ⟨2794, c2794, 4000, checked2794⟩,
  ⟨2795, c2795, 4000, checked2795⟩,
  ⟨2796, c2796, 4000, checked2796⟩,
  ⟨2797, c2797, 4000, checked2797⟩,
  ⟨2798, c2798, 4000, checked2798⟩,
  ⟨2799, c2799, 4000, checked2799⟩,
  ⟨2800, c2800, 4000, checked2800⟩,
  ⟨2801, c2801, 4000, checked2801⟩,
  ⟨2802, c2802, 4000, checked2802⟩,
  ⟨2803, c2803, 4000, checked2803⟩,
  ⟨2804, c2804, 4000, checked2804⟩,
  ⟨2805, c2805, 4000, checked2805⟩]

end PA215.ContractShards.Shard021Part6
