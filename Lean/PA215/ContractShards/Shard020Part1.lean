import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C020
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard020Part1
open PA215.Contracts PA215.Census

def original2582 : RawOriginal := C020.records[22]'(by decide)
theorem original_id2582 : original2582.index = 2582 := by decide

def c2582 : Contract := original2582.toContract.get (by decide)
theorem binding2582 : original2582.toContract = some c2582 := rfl

theorem checked2582 : check 4000 c2582 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2583 : RawOriginal := C020.records[23]'(by decide)
theorem original_id2583 : original2583.index = 2583 := by decide

def c2583 : Contract := original2583.toContract.get (by decide)
theorem binding2583 : original2583.toContract = some c2583 := rfl

theorem checked2583 : check 4000 c2583 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2584 : RawOriginal := C020.records[24]'(by decide)
theorem original_id2584 : original2584.index = 2584 := by decide

def c2584 : Contract := original2584.toContract.get (by decide)
theorem binding2584 : original2584.toContract = some c2584 := rfl

theorem checked2584 : check 4000 c2584 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2585 : RawOriginal := C020.records[25]'(by decide)
theorem original_id2585 : original2585.index = 2585 := by decide

def c2585 : Contract := original2585.toContract.get (by decide)
theorem binding2585 : original2585.toContract = some c2585 := rfl

theorem checked2585 : check 4000 c2585 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2586 : RawOriginal := C020.records[26]'(by decide)
theorem original_id2586 : original2586.index = 2586 := by decide

def c2586 : Contract := original2586.toContract.get (by decide)
theorem binding2586 : original2586.toContract = some c2586 := rfl

theorem checked2586 : check 4000 c2586 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2587 : RawOriginal := C020.records[27]'(by decide)
theorem original_id2587 : original2587.index = 2587 := by decide

def c2587 : Contract := original2587.toContract.get (by decide)
theorem binding2587 : original2587.toContract = some c2587 := rfl

theorem checked2587 : check 4000 c2587 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2588 : RawOriginal := C020.records[28]'(by decide)
theorem original_id2588 : original2588.index = 2588 := by decide

def c2588 : Contract := original2588.toContract.get (by decide)
theorem binding2588 : original2588.toContract = some c2588 := rfl

theorem checked2588 : check 4000 c2588 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2589 : RawOriginal := C020.records[29]'(by decide)
theorem original_id2589 : original2589.index = 2589 := by decide

def c2589 : Contract := original2589.toContract.get (by decide)
theorem binding2589 : original2589.toContract = some c2589 := rfl

theorem checked2589 : check 4000 c2589 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2590 : RawOriginal := C020.records[30]'(by decide)
theorem original_id2590 : original2590.index = 2590 := by decide

def c2590 : Contract := original2590.toContract.get (by decide)
theorem binding2590 : original2590.toContract = some c2590 := rfl

theorem checked2590 : check 4000 c2590 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2591 : RawOriginal := C020.records[31]'(by decide)
theorem original_id2591 : original2591.index = 2591 := by decide

def c2591 : Contract := original2591.toContract.get (by decide)
theorem binding2591 : original2591.toContract = some c2591 := rfl

theorem checked2591 : check 4000 c2591 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2592 : RawOriginal := C020.records[32]'(by decide)
theorem original_id2592 : original2592.index = 2592 := by decide

def c2592 : Contract := original2592.toContract.get (by decide)
theorem binding2592 : original2592.toContract = some c2592 := rfl

theorem checked2592 : check 4000 c2592 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2593 : RawOriginal := C020.records[33]'(by decide)
theorem original_id2593 : original2593.index = 2593 := by decide

def c2593 : Contract := original2593.toContract.get (by decide)
theorem binding2593 : original2593.toContract = some c2593 := rfl

theorem checked2593 : check 4000 c2593 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2594 : RawOriginal := C020.records[34]'(by decide)
theorem original_id2594 : original2594.index = 2594 := by decide

def c2594 : Contract := original2594.toContract.get (by decide)
theorem binding2594 : original2594.toContract = some c2594 := rfl

theorem checked2594 : check 4000 c2594 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2595 : RawOriginal := C020.records[35]'(by decide)
theorem original_id2595 : original2595.index = 2595 := by decide

def c2595 : Contract := original2595.toContract.get (by decide)
theorem binding2595 : original2595.toContract = some c2595 := rfl

theorem checked2595 : check 4000 c2595 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2596 : RawOriginal := C020.records[36]'(by decide)
theorem original_id2596 : original2596.index = 2596 := by decide

def c2596 : Contract := original2596.toContract.get (by decide)
theorem binding2596 : original2596.toContract = some c2596 := rfl

theorem checked2596 : check 4000 c2596 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2597 : RawOriginal := C020.records[37]'(by decide)
theorem original_id2597 : original2597.index = 2597 := by decide

def c2597 : Contract := original2597.toContract.get (by decide)
theorem binding2597 : original2597.toContract = some c2597 := rfl

theorem checked2597 : check 4000 c2597 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2582, c2582, 4000, checked2582⟩,
  ⟨2583, c2583, 4000, checked2583⟩,
  ⟨2584, c2584, 4000, checked2584⟩,
  ⟨2585, c2585, 4000, checked2585⟩,
  ⟨2586, c2586, 4000, checked2586⟩,
  ⟨2587, c2587, 4000, checked2587⟩,
  ⟨2588, c2588, 4000, checked2588⟩,
  ⟨2589, c2589, 4000, checked2589⟩,
  ⟨2590, c2590, 4000, checked2590⟩,
  ⟨2591, c2591, 4000, checked2591⟩,
  ⟨2592, c2592, 4000, checked2592⟩,
  ⟨2593, c2593, 4000, checked2593⟩,
  ⟨2594, c2594, 4000, checked2594⟩,
  ⟨2595, c2595, 4000, checked2595⟩,
  ⟨2596, c2596, 4000, checked2596⟩,
  ⟨2597, c2597, 4000, checked2597⟩]

end PA215.ContractShards.Shard020Part1
