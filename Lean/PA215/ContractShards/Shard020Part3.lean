import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C020
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard020Part3
open PA215.Contracts PA215.Census

def original2614 : RawOriginal := C020.records[54]'(by decide)
theorem original_id2614 : original2614.index = 2614 := by decide

def c2614 : Contract := original2614.toContract.get (by decide)
theorem binding2614 : original2614.toContract = some c2614 := rfl

theorem checked2614 : check 4000 c2614 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2615 : RawOriginal := C020.records[55]'(by decide)
theorem original_id2615 : original2615.index = 2615 := by decide

def c2615 : Contract := original2615.toContract.get (by decide)
theorem binding2615 : original2615.toContract = some c2615 := rfl

theorem checked2615 : check 4000 c2615 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2616 : RawOriginal := C020.records[56]'(by decide)
theorem original_id2616 : original2616.index = 2616 := by decide

def c2616 : Contract := original2616.toContract.get (by decide)
theorem binding2616 : original2616.toContract = some c2616 := rfl

theorem checked2616 : check 4000 c2616 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2617 : RawOriginal := C020.records[57]'(by decide)
theorem original_id2617 : original2617.index = 2617 := by decide

def c2617 : Contract := original2617.toContract.get (by decide)
theorem binding2617 : original2617.toContract = some c2617 := rfl

theorem checked2617 : check 4000 c2617 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2618 : RawOriginal := C020.records[58]'(by decide)
theorem original_id2618 : original2618.index = 2618 := by decide

def c2618 : Contract := original2618.toContract.get (by decide)
theorem binding2618 : original2618.toContract = some c2618 := rfl

theorem checked2618 : check 4000 c2618 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2619 : RawOriginal := C020.records[59]'(by decide)
theorem original_id2619 : original2619.index = 2619 := by decide

def c2619 : Contract := original2619.toContract.get (by decide)
theorem binding2619 : original2619.toContract = some c2619 := rfl

theorem checked2619 : check 4000 c2619 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2620 : RawOriginal := C020.records[60]'(by decide)
theorem original_id2620 : original2620.index = 2620 := by decide

def c2620 : Contract := original2620.toContract.get (by decide)
theorem binding2620 : original2620.toContract = some c2620 := rfl

theorem checked2620 : check 4000 c2620 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2621 : RawOriginal := C020.records[61]'(by decide)
theorem original_id2621 : original2621.index = 2621 := by decide

def c2621 : Contract := original2621.toContract.get (by decide)
theorem binding2621 : original2621.toContract = some c2621 := rfl

theorem checked2621 : check 4000 c2621 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2622 : RawOriginal := C020.records[62]'(by decide)
theorem original_id2622 : original2622.index = 2622 := by decide

def c2622 : Contract := original2622.toContract.get (by decide)
theorem binding2622 : original2622.toContract = some c2622 := rfl

theorem checked2622 : check 4000 c2622 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2623 : RawOriginal := C020.records[63]'(by decide)
theorem original_id2623 : original2623.index = 2623 := by decide

def c2623 : Contract := original2623.toContract.get (by decide)
theorem binding2623 : original2623.toContract = some c2623 := rfl

theorem checked2623 : check 4000 c2623 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2624 : RawOriginal := C020.records[64]'(by decide)
theorem original_id2624 : original2624.index = 2624 := by decide

def c2624 : Contract := original2624.toContract.get (by decide)
theorem binding2624 : original2624.toContract = some c2624 := rfl

theorem checked2624 : check 4000 c2624 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2625 : RawOriginal := C020.records[65]'(by decide)
theorem original_id2625 : original2625.index = 2625 := by decide

def c2625 : Contract := original2625.toContract.get (by decide)
theorem binding2625 : original2625.toContract = some c2625 := rfl

theorem checked2625 : check 4000 c2625 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2626 : RawOriginal := C020.records[66]'(by decide)
theorem original_id2626 : original2626.index = 2626 := by decide

def c2626 : Contract := original2626.toContract.get (by decide)
theorem binding2626 : original2626.toContract = some c2626 := rfl

theorem checked2626 : check 4000 c2626 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2627 : RawOriginal := C020.records[67]'(by decide)
theorem original_id2627 : original2627.index = 2627 := by decide

def c2627 : Contract := original2627.toContract.get (by decide)
theorem binding2627 : original2627.toContract = some c2627 := rfl

theorem checked2627 : check 4000 c2627 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2628 : RawOriginal := C020.records[68]'(by decide)
theorem original_id2628 : original2628.index = 2628 := by decide

def c2628 : Contract := original2628.toContract.get (by decide)
theorem binding2628 : original2628.toContract = some c2628 := rfl

theorem checked2628 : check 4000 c2628 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2629 : RawOriginal := C020.records[69]'(by decide)
theorem original_id2629 : original2629.index = 2629 := by decide

def c2629 : Contract := original2629.toContract.get (by decide)
theorem binding2629 : original2629.toContract = some c2629 := rfl

theorem checked2629 : check 4000 c2629 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2614, c2614, 4000, checked2614⟩,
  ⟨2615, c2615, 4000, checked2615⟩,
  ⟨2616, c2616, 4000, checked2616⟩,
  ⟨2617, c2617, 4000, checked2617⟩,
  ⟨2618, c2618, 4000, checked2618⟩,
  ⟨2619, c2619, 4000, checked2619⟩,
  ⟨2620, c2620, 4000, checked2620⟩,
  ⟨2621, c2621, 4000, checked2621⟩,
  ⟨2622, c2622, 4000, checked2622⟩,
  ⟨2623, c2623, 4000, checked2623⟩,
  ⟨2624, c2624, 4000, checked2624⟩,
  ⟨2625, c2625, 4000, checked2625⟩,
  ⟨2626, c2626, 4000, checked2626⟩,
  ⟨2627, c2627, 4000, checked2627⟩,
  ⟨2628, c2628, 4000, checked2628⟩,
  ⟨2629, c2629, 4000, checked2629⟩]

end PA215.ContractShards.Shard020Part3
