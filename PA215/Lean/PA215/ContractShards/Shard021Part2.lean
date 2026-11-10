import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C021
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard021Part2
open PA215.Contracts PA215.Census

def original2726 : RawOriginal := C021.records[38]'(by decide)
theorem original_id2726 : original2726.index = 2726 := by decide

def c2726 : Contract := original2726.toContract.get (by decide)
theorem binding2726 : original2726.toContract = some c2726 := rfl

theorem checked2726 : check 4000 c2726 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2727 : RawOriginal := C021.records[39]'(by decide)
theorem original_id2727 : original2727.index = 2727 := by decide

def c2727 : Contract := original2727.toContract.get (by decide)
theorem binding2727 : original2727.toContract = some c2727 := rfl

theorem checked2727 : check 4000 c2727 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2728 : RawOriginal := C021.records[40]'(by decide)
theorem original_id2728 : original2728.index = 2728 := by decide

def c2728 : Contract := original2728.toContract.get (by decide)
theorem binding2728 : original2728.toContract = some c2728 := rfl

theorem checked2728 : check 4000 c2728 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2729 : RawOriginal := C021.records[41]'(by decide)
theorem original_id2729 : original2729.index = 2729 := by decide

def c2729 : Contract := original2729.toContract.get (by decide)
theorem binding2729 : original2729.toContract = some c2729 := rfl

theorem checked2729 : check 4000 c2729 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2730 : RawOriginal := C021.records[42]'(by decide)
theorem original_id2730 : original2730.index = 2730 := by decide

def c2730 : Contract := original2730.toContract.get (by decide)
theorem binding2730 : original2730.toContract = some c2730 := rfl

theorem checked2730 : check 4000 c2730 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2731 : RawOriginal := C021.records[43]'(by decide)
theorem original_id2731 : original2731.index = 2731 := by decide

def c2731 : Contract := original2731.toContract.get (by decide)
theorem binding2731 : original2731.toContract = some c2731 := rfl

theorem checked2731 : check 4000 c2731 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2732 : RawOriginal := C021.records[44]'(by decide)
theorem original_id2732 : original2732.index = 2732 := by decide

def c2732 : Contract := original2732.toContract.get (by decide)
theorem binding2732 : original2732.toContract = some c2732 := rfl

theorem checked2732 : check 4000 c2732 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2733 : RawOriginal := C021.records[45]'(by decide)
theorem original_id2733 : original2733.index = 2733 := by decide

def c2733 : Contract := original2733.toContract.get (by decide)
theorem binding2733 : original2733.toContract = some c2733 := rfl

theorem checked2733 : check 4000 c2733 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2734 : RawOriginal := C021.records[46]'(by decide)
theorem original_id2734 : original2734.index = 2734 := by decide

def c2734 : Contract := original2734.toContract.get (by decide)
theorem binding2734 : original2734.toContract = some c2734 := rfl

theorem checked2734 : check 4000 c2734 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2735 : RawOriginal := C021.records[47]'(by decide)
theorem original_id2735 : original2735.index = 2735 := by decide

def c2735 : Contract := original2735.toContract.get (by decide)
theorem binding2735 : original2735.toContract = some c2735 := rfl

theorem checked2735 : check 4000 c2735 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2736 : RawOriginal := C021.records[48]'(by decide)
theorem original_id2736 : original2736.index = 2736 := by decide

def c2736 : Contract := original2736.toContract.get (by decide)
theorem binding2736 : original2736.toContract = some c2736 := rfl

theorem checked2736 : check 4000 c2736 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2737 : RawOriginal := C021.records[49]'(by decide)
theorem original_id2737 : original2737.index = 2737 := by decide

def c2737 : Contract := original2737.toContract.get (by decide)
theorem binding2737 : original2737.toContract = some c2737 := rfl

theorem checked2737 : check 4000 c2737 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2738 : RawOriginal := C021.records[50]'(by decide)
theorem original_id2738 : original2738.index = 2738 := by decide

def c2738 : Contract := original2738.toContract.get (by decide)
theorem binding2738 : original2738.toContract = some c2738 := rfl

theorem checked2738 : check 4000 c2738 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2739 : RawOriginal := C021.records[51]'(by decide)
theorem original_id2739 : original2739.index = 2739 := by decide

def c2739 : Contract := original2739.toContract.get (by decide)
theorem binding2739 : original2739.toContract = some c2739 := rfl

theorem checked2739 : check 4000 c2739 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2740 : RawOriginal := C021.records[52]'(by decide)
theorem original_id2740 : original2740.index = 2740 := by decide

def c2740 : Contract := original2740.toContract.get (by decide)
theorem binding2740 : original2740.toContract = some c2740 := rfl

theorem checked2740 : check 4000 c2740 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2741 : RawOriginal := C021.records[53]'(by decide)
theorem original_id2741 : original2741.index = 2741 := by decide

def c2741 : Contract := original2741.toContract.get (by decide)
theorem binding2741 : original2741.toContract = some c2741 := rfl

theorem checked2741 : check 4000 c2741 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2726, c2726, 4000, checked2726⟩,
  ⟨2727, c2727, 4000, checked2727⟩,
  ⟨2728, c2728, 4000, checked2728⟩,
  ⟨2729, c2729, 4000, checked2729⟩,
  ⟨2730, c2730, 4000, checked2730⟩,
  ⟨2731, c2731, 4000, checked2731⟩,
  ⟨2732, c2732, 4000, checked2732⟩,
  ⟨2733, c2733, 4000, checked2733⟩,
  ⟨2734, c2734, 4000, checked2734⟩,
  ⟨2735, c2735, 4000, checked2735⟩,
  ⟨2736, c2736, 4000, checked2736⟩,
  ⟨2737, c2737, 4000, checked2737⟩,
  ⟨2738, c2738, 4000, checked2738⟩,
  ⟨2739, c2739, 4000, checked2739⟩,
  ⟨2740, c2740, 4000, checked2740⟩,
  ⟨2741, c2741, 4000, checked2741⟩]

end PA215.ContractShards.Shard021Part2
