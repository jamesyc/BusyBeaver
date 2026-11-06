import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C020
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard020Part6
open PA215.Contracts PA215.Census

def original2662 : RawOriginal := C020.records[102]'(by decide)
theorem original_id2662 : original2662.index = 2662 := by decide

def c2662 : Contract := original2662.toContract.get (by decide)
theorem binding2662 : original2662.toContract = some c2662 := rfl

theorem checked2662 : check 4000 c2662 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2663 : RawOriginal := C020.records[103]'(by decide)
theorem original_id2663 : original2663.index = 2663 := by decide

def c2663 : Contract := original2663.toContract.get (by decide)
theorem binding2663 : original2663.toContract = some c2663 := rfl

theorem checked2663 : check 4000 c2663 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2664 : RawOriginal := C020.records[104]'(by decide)
theorem original_id2664 : original2664.index = 2664 := by decide

def c2664 : Contract := original2664.toContract.get (by decide)
theorem binding2664 : original2664.toContract = some c2664 := rfl

theorem checked2664 : check 4000 c2664 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2665 : RawOriginal := C020.records[105]'(by decide)
theorem original_id2665 : original2665.index = 2665 := by decide

def c2665 : Contract := original2665.toContract.get (by decide)
theorem binding2665 : original2665.toContract = some c2665 := rfl

theorem checked2665 : check 4000 c2665 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2666 : RawOriginal := C020.records[106]'(by decide)
theorem original_id2666 : original2666.index = 2666 := by decide

def c2666 : Contract := original2666.toContract.get (by decide)
theorem binding2666 : original2666.toContract = some c2666 := rfl

theorem checked2666 : check 4000 c2666 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2667 : RawOriginal := C020.records[107]'(by decide)
theorem original_id2667 : original2667.index = 2667 := by decide

def c2667 : Contract := original2667.toContract.get (by decide)
theorem binding2667 : original2667.toContract = some c2667 := rfl

theorem checked2667 : check 4000 c2667 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2668 : RawOriginal := C020.records[108]'(by decide)
theorem original_id2668 : original2668.index = 2668 := by decide

def c2668 : Contract := original2668.toContract.get (by decide)
theorem binding2668 : original2668.toContract = some c2668 := rfl

theorem checked2668 : check 4000 c2668 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2669 : RawOriginal := C020.records[109]'(by decide)
theorem original_id2669 : original2669.index = 2669 := by decide

def c2669 : Contract := original2669.toContract.get (by decide)
theorem binding2669 : original2669.toContract = some c2669 := rfl

theorem checked2669 : check 4000 c2669 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2670 : RawOriginal := C020.records[110]'(by decide)
theorem original_id2670 : original2670.index = 2670 := by decide

def c2670 : Contract := original2670.toContract.get (by decide)
theorem binding2670 : original2670.toContract = some c2670 := rfl

theorem checked2670 : check 4000 c2670 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2671 : RawOriginal := C020.records[111]'(by decide)
theorem original_id2671 : original2671.index = 2671 := by decide

def c2671 : Contract := original2671.toContract.get (by decide)
theorem binding2671 : original2671.toContract = some c2671 := rfl

theorem checked2671 : check 4000 c2671 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2672 : RawOriginal := C020.records[112]'(by decide)
theorem original_id2672 : original2672.index = 2672 := by decide

def c2672 : Contract := original2672.toContract.get (by decide)
theorem binding2672 : original2672.toContract = some c2672 := rfl

theorem checked2672 : check 4000 c2672 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2673 : RawOriginal := C020.records[113]'(by decide)
theorem original_id2673 : original2673.index = 2673 := by decide

def c2673 : Contract := original2673.toContract.get (by decide)
theorem binding2673 : original2673.toContract = some c2673 := rfl

theorem checked2673 : check 4000 c2673 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2674 : RawOriginal := C020.records[114]'(by decide)
theorem original_id2674 : original2674.index = 2674 := by decide

def c2674 : Contract := original2674.toContract.get (by decide)
theorem binding2674 : original2674.toContract = some c2674 := rfl

theorem checked2674 : check 4000 c2674 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2675 : RawOriginal := C020.records[115]'(by decide)
theorem original_id2675 : original2675.index = 2675 := by decide

def c2675 : Contract := original2675.toContract.get (by decide)
theorem binding2675 : original2675.toContract = some c2675 := rfl

theorem checked2675 : check 4000 c2675 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2676 : RawOriginal := C020.records[116]'(by decide)
theorem original_id2676 : original2676.index = 2676 := by decide

def c2676 : Contract := original2676.toContract.get (by decide)
theorem binding2676 : original2676.toContract = some c2676 := rfl

theorem checked2676 : check 4000 c2676 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2677 : RawOriginal := C020.records[117]'(by decide)
theorem original_id2677 : original2677.index = 2677 := by decide

def c2677 : Contract := original2677.toContract.get (by decide)
theorem binding2677 : original2677.toContract = some c2677 := rfl

theorem checked2677 : check 4000 c2677 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2662, c2662, 4000, checked2662⟩,
  ⟨2663, c2663, 4000, checked2663⟩,
  ⟨2664, c2664, 4000, checked2664⟩,
  ⟨2665, c2665, 4000, checked2665⟩,
  ⟨2666, c2666, 4000, checked2666⟩,
  ⟨2667, c2667, 4000, checked2667⟩,
  ⟨2668, c2668, 4000, checked2668⟩,
  ⟨2669, c2669, 4000, checked2669⟩,
  ⟨2670, c2670, 4000, checked2670⟩,
  ⟨2671, c2671, 4000, checked2671⟩,
  ⟨2672, c2672, 4000, checked2672⟩,
  ⟨2673, c2673, 4000, checked2673⟩,
  ⟨2674, c2674, 4000, checked2674⟩,
  ⟨2675, c2675, 4000, checked2675⟩,
  ⟨2676, c2676, 4000, checked2676⟩,
  ⟨2677, c2677, 4000, checked2677⟩]

end PA215.ContractShards.Shard020Part6
