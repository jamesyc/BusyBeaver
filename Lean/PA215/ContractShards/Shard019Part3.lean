import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C019
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard019Part3
open PA215.Contracts PA215.Census

def original2486 : RawOriginal := C019.records[54]'(by decide)
theorem original_id2486 : original2486.index = 2486 := by decide

def c2486 : Contract := original2486.toContract.get (by decide)
theorem binding2486 : original2486.toContract = some c2486 := rfl

theorem checked2486 : check 4000 c2486 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2487 : RawOriginal := C019.records[55]'(by decide)
theorem original_id2487 : original2487.index = 2487 := by decide

def c2487 : Contract := original2487.toContract.get (by decide)
theorem binding2487 : original2487.toContract = some c2487 := rfl

theorem checked2487 : check 4000 c2487 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2488 : RawOriginal := C019.records[56]'(by decide)
theorem original_id2488 : original2488.index = 2488 := by decide

def c2488 : Contract := original2488.toContract.get (by decide)
theorem binding2488 : original2488.toContract = some c2488 := rfl

theorem checked2488 : check 4000 c2488 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2489 : RawOriginal := C019.records[57]'(by decide)
theorem original_id2489 : original2489.index = 2489 := by decide

def c2489 : Contract := original2489.toContract.get (by decide)
theorem binding2489 : original2489.toContract = some c2489 := rfl

theorem checked2489 : check 4000 c2489 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2490 : RawOriginal := C019.records[58]'(by decide)
theorem original_id2490 : original2490.index = 2490 := by decide

def c2490 : Contract := original2490.toContract.get (by decide)
theorem binding2490 : original2490.toContract = some c2490 := rfl

theorem checked2490 : check 4000 c2490 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2491 : RawOriginal := C019.records[59]'(by decide)
theorem original_id2491 : original2491.index = 2491 := by decide

def c2491 : Contract := original2491.toContract.get (by decide)
theorem binding2491 : original2491.toContract = some c2491 := rfl

theorem checked2491 : check 4000 c2491 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2492 : RawOriginal := C019.records[60]'(by decide)
theorem original_id2492 : original2492.index = 2492 := by decide

def c2492 : Contract := original2492.toContract.get (by decide)
theorem binding2492 : original2492.toContract = some c2492 := rfl

theorem checked2492 : check 4000 c2492 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2493 : RawOriginal := C019.records[61]'(by decide)
theorem original_id2493 : original2493.index = 2493 := by decide

def c2493 : Contract := original2493.toContract.get (by decide)
theorem binding2493 : original2493.toContract = some c2493 := rfl

theorem checked2493 : check 4000 c2493 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2494 : RawOriginal := C019.records[62]'(by decide)
theorem original_id2494 : original2494.index = 2494 := by decide

def c2494 : Contract := original2494.toContract.get (by decide)
theorem binding2494 : original2494.toContract = some c2494 := rfl

theorem checked2494 : check 4000 c2494 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2495 : RawOriginal := C019.records[63]'(by decide)
theorem original_id2495 : original2495.index = 2495 := by decide

def c2495 : Contract := original2495.toContract.get (by decide)
theorem binding2495 : original2495.toContract = some c2495 := rfl

theorem checked2495 : check 4000 c2495 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2496 : RawOriginal := C019.records[64]'(by decide)
theorem original_id2496 : original2496.index = 2496 := by decide

def c2496 : Contract := original2496.toContract.get (by decide)
theorem binding2496 : original2496.toContract = some c2496 := rfl

theorem checked2496 : check 4000 c2496 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2497 : RawOriginal := C019.records[65]'(by decide)
theorem original_id2497 : original2497.index = 2497 := by decide

def c2497 : Contract := original2497.toContract.get (by decide)
theorem binding2497 : original2497.toContract = some c2497 := rfl

theorem checked2497 : check 4000 c2497 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2498 : RawOriginal := C019.records[66]'(by decide)
theorem original_id2498 : original2498.index = 2498 := by decide

def c2498 : Contract := original2498.toContract.get (by decide)
theorem binding2498 : original2498.toContract = some c2498 := rfl

theorem checked2498 : check 4000 c2498 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2499 : RawOriginal := C019.records[67]'(by decide)
theorem original_id2499 : original2499.index = 2499 := by decide

def c2499 : Contract := original2499.toContract.get (by decide)
theorem binding2499 : original2499.toContract = some c2499 := rfl

theorem checked2499 : check 4000 c2499 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2500 : RawOriginal := C019.records[68]'(by decide)
theorem original_id2500 : original2500.index = 2500 := by decide

def c2500 : Contract := original2500.toContract.get (by decide)
theorem binding2500 : original2500.toContract = some c2500 := rfl

theorem checked2500 : check 4000 c2500 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2501 : RawOriginal := C019.records[69]'(by decide)
theorem original_id2501 : original2501.index = 2501 := by decide

def c2501 : Contract := original2501.toContract.get (by decide)
theorem binding2501 : original2501.toContract = some c2501 := rfl

theorem checked2501 : check 4000 c2501 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2486, c2486, 4000, checked2486⟩,
  ⟨2487, c2487, 4000, checked2487⟩,
  ⟨2488, c2488, 4000, checked2488⟩,
  ⟨2489, c2489, 4000, checked2489⟩,
  ⟨2490, c2490, 4000, checked2490⟩,
  ⟨2491, c2491, 4000, checked2491⟩,
  ⟨2492, c2492, 4000, checked2492⟩,
  ⟨2493, c2493, 4000, checked2493⟩,
  ⟨2494, c2494, 4000, checked2494⟩,
  ⟨2495, c2495, 4000, checked2495⟩,
  ⟨2496, c2496, 4000, checked2496⟩,
  ⟨2497, c2497, 4000, checked2497⟩,
  ⟨2498, c2498, 4000, checked2498⟩,
  ⟨2499, c2499, 4000, checked2499⟩,
  ⟨2500, c2500, 4000, checked2500⟩,
  ⟨2501, c2501, 4000, checked2501⟩]

end PA215.ContractShards.Shard019Part3
