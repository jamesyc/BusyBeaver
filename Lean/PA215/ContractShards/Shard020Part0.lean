import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C020
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard020Part0
open PA215.Contracts PA215.Census

def original2566 : RawOriginal := C020.records[6]'(by decide)
theorem original_id2566 : original2566.index = 2566 := by decide

def c2566 : Contract := original2566.toContract.get (by decide)
theorem binding2566 : original2566.toContract = some c2566 := rfl

theorem checked2566 : check 4000 c2566 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2567 : RawOriginal := C020.records[7]'(by decide)
theorem original_id2567 : original2567.index = 2567 := by decide

def c2567 : Contract := original2567.toContract.get (by decide)
theorem binding2567 : original2567.toContract = some c2567 := rfl

theorem checked2567 : check 4000 c2567 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2568 : RawOriginal := C020.records[8]'(by decide)
theorem original_id2568 : original2568.index = 2568 := by decide

def c2568 : Contract := original2568.toContract.get (by decide)
theorem binding2568 : original2568.toContract = some c2568 := rfl

theorem checked2568 : check 4000 c2568 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2569 : RawOriginal := C020.records[9]'(by decide)
theorem original_id2569 : original2569.index = 2569 := by decide

def c2569 : Contract := original2569.toContract.get (by decide)
theorem binding2569 : original2569.toContract = some c2569 := rfl

theorem checked2569 : check 4000 c2569 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2570 : RawOriginal := C020.records[10]'(by decide)
theorem original_id2570 : original2570.index = 2570 := by decide

def c2570 : Contract := original2570.toContract.get (by decide)
theorem binding2570 : original2570.toContract = some c2570 := rfl

theorem checked2570 : check 4000 c2570 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2571 : RawOriginal := C020.records[11]'(by decide)
theorem original_id2571 : original2571.index = 2571 := by decide

def c2571 : Contract := original2571.toContract.get (by decide)
theorem binding2571 : original2571.toContract = some c2571 := rfl

theorem checked2571 : check 4000 c2571 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2572 : RawOriginal := C020.records[12]'(by decide)
theorem original_id2572 : original2572.index = 2572 := by decide

def c2572 : Contract := original2572.toContract.get (by decide)
theorem binding2572 : original2572.toContract = some c2572 := rfl

theorem checked2572 : check 4000 c2572 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2573 : RawOriginal := C020.records[13]'(by decide)
theorem original_id2573 : original2573.index = 2573 := by decide

def c2573 : Contract := original2573.toContract.get (by decide)
theorem binding2573 : original2573.toContract = some c2573 := rfl

theorem checked2573 : check 4000 c2573 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2574 : RawOriginal := C020.records[14]'(by decide)
theorem original_id2574 : original2574.index = 2574 := by decide

def c2574 : Contract := original2574.toContract.get (by decide)
theorem binding2574 : original2574.toContract = some c2574 := rfl

theorem checked2574 : check 4000 c2574 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2575 : RawOriginal := C020.records[15]'(by decide)
theorem original_id2575 : original2575.index = 2575 := by decide

def c2575 : Contract := original2575.toContract.get (by decide)
theorem binding2575 : original2575.toContract = some c2575 := rfl

theorem checked2575 : check 4000 c2575 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2576 : RawOriginal := C020.records[16]'(by decide)
theorem original_id2576 : original2576.index = 2576 := by decide

def c2576 : Contract := original2576.toContract.get (by decide)
theorem binding2576 : original2576.toContract = some c2576 := rfl

theorem checked2576 : check 4000 c2576 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2577 : RawOriginal := C020.records[17]'(by decide)
theorem original_id2577 : original2577.index = 2577 := by decide

def c2577 : Contract := original2577.toContract.get (by decide)
theorem binding2577 : original2577.toContract = some c2577 := rfl

theorem checked2577 : check 4000 c2577 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2578 : RawOriginal := C020.records[18]'(by decide)
theorem original_id2578 : original2578.index = 2578 := by decide

def c2578 : Contract := original2578.toContract.get (by decide)
theorem binding2578 : original2578.toContract = some c2578 := rfl

theorem checked2578 : check 4000 c2578 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2579 : RawOriginal := C020.records[19]'(by decide)
theorem original_id2579 : original2579.index = 2579 := by decide

def c2579 : Contract := original2579.toContract.get (by decide)
theorem binding2579 : original2579.toContract = some c2579 := rfl

theorem checked2579 : check 4000 c2579 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2580 : RawOriginal := C020.records[20]'(by decide)
theorem original_id2580 : original2580.index = 2580 := by decide

def c2580 : Contract := original2580.toContract.get (by decide)
theorem binding2580 : original2580.toContract = some c2580 := rfl

theorem checked2580 : check 4000 c2580 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2581 : RawOriginal := C020.records[21]'(by decide)
theorem original_id2581 : original2581.index = 2581 := by decide

def c2581 : Contract := original2581.toContract.get (by decide)
theorem binding2581 : original2581.toContract = some c2581 := rfl

theorem checked2581 : check 4000 c2581 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2566, c2566, 4000, checked2566⟩,
  ⟨2567, c2567, 4000, checked2567⟩,
  ⟨2568, c2568, 4000, checked2568⟩,
  ⟨2569, c2569, 4000, checked2569⟩,
  ⟨2570, c2570, 4000, checked2570⟩,
  ⟨2571, c2571, 4000, checked2571⟩,
  ⟨2572, c2572, 4000, checked2572⟩,
  ⟨2573, c2573, 4000, checked2573⟩,
  ⟨2574, c2574, 4000, checked2574⟩,
  ⟨2575, c2575, 4000, checked2575⟩,
  ⟨2576, c2576, 4000, checked2576⟩,
  ⟨2577, c2577, 4000, checked2577⟩,
  ⟨2578, c2578, 4000, checked2578⟩,
  ⟨2579, c2579, 4000, checked2579⟩,
  ⟨2580, c2580, 4000, checked2580⟩,
  ⟨2581, c2581, 4000, checked2581⟩]

end PA215.ContractShards.Shard020Part0
