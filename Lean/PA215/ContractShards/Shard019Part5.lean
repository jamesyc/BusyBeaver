import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C019
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard019Part5
open PA215.Contracts PA215.Census

def original2518 : RawOriginal := C019.records[86]'(by decide)
theorem original_id2518 : original2518.index = 2518 := by decide

def c2518 : Contract := original2518.toContract.get (by decide)
theorem binding2518 : original2518.toContract = some c2518 := rfl

theorem checked2518 : check 4000 c2518 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2519 : RawOriginal := C019.records[87]'(by decide)
theorem original_id2519 : original2519.index = 2519 := by decide

def c2519 : Contract := original2519.toContract.get (by decide)
theorem binding2519 : original2519.toContract = some c2519 := rfl

theorem checked2519 : check 4000 c2519 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2520 : RawOriginal := C019.records[88]'(by decide)
theorem original_id2520 : original2520.index = 2520 := by decide

def c2520 : Contract := original2520.toContract.get (by decide)
theorem binding2520 : original2520.toContract = some c2520 := rfl

theorem checked2520 : check 4000 c2520 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2521 : RawOriginal := C019.records[89]'(by decide)
theorem original_id2521 : original2521.index = 2521 := by decide

def c2521 : Contract := original2521.toContract.get (by decide)
theorem binding2521 : original2521.toContract = some c2521 := rfl

theorem checked2521 : check 4000 c2521 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2522 : RawOriginal := C019.records[90]'(by decide)
theorem original_id2522 : original2522.index = 2522 := by decide

def c2522 : Contract := original2522.toContract.get (by decide)
theorem binding2522 : original2522.toContract = some c2522 := rfl

theorem checked2522 : check 4000 c2522 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2523 : RawOriginal := C019.records[91]'(by decide)
theorem original_id2523 : original2523.index = 2523 := by decide

def c2523 : Contract := original2523.toContract.get (by decide)
theorem binding2523 : original2523.toContract = some c2523 := rfl

theorem checked2523 : check 4000 c2523 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2524 : RawOriginal := C019.records[92]'(by decide)
theorem original_id2524 : original2524.index = 2524 := by decide

def c2524 : Contract := original2524.toContract.get (by decide)
theorem binding2524 : original2524.toContract = some c2524 := rfl

theorem checked2524 : check 4000 c2524 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2525 : RawOriginal := C019.records[93]'(by decide)
theorem original_id2525 : original2525.index = 2525 := by decide

def c2525 : Contract := original2525.toContract.get (by decide)
theorem binding2525 : original2525.toContract = some c2525 := rfl

theorem checked2525 : check 4000 c2525 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2526 : RawOriginal := C019.records[94]'(by decide)
theorem original_id2526 : original2526.index = 2526 := by decide

def c2526 : Contract := original2526.toContract.get (by decide)
theorem binding2526 : original2526.toContract = some c2526 := rfl

theorem checked2526 : check 4000 c2526 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2527 : RawOriginal := C019.records[95]'(by decide)
theorem original_id2527 : original2527.index = 2527 := by decide

def c2527 : Contract := original2527.toContract.get (by decide)
theorem binding2527 : original2527.toContract = some c2527 := rfl

theorem checked2527 : check 4000 c2527 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2528 : RawOriginal := C019.records[96]'(by decide)
theorem original_id2528 : original2528.index = 2528 := by decide

def c2528 : Contract := original2528.toContract.get (by decide)
theorem binding2528 : original2528.toContract = some c2528 := rfl

theorem checked2528 : check 4000 c2528 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2529 : RawOriginal := C019.records[97]'(by decide)
theorem original_id2529 : original2529.index = 2529 := by decide

def c2529 : Contract := original2529.toContract.get (by decide)
theorem binding2529 : original2529.toContract = some c2529 := rfl

theorem checked2529 : check 4000 c2529 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2530 : RawOriginal := C019.records[98]'(by decide)
theorem original_id2530 : original2530.index = 2530 := by decide

def c2530 : Contract := original2530.toContract.get (by decide)
theorem binding2530 : original2530.toContract = some c2530 := rfl

theorem checked2530 : check 4000 c2530 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2531 : RawOriginal := C019.records[99]'(by decide)
theorem original_id2531 : original2531.index = 2531 := by decide

def c2531 : Contract := original2531.toContract.get (by decide)
theorem binding2531 : original2531.toContract = some c2531 := rfl

theorem checked2531 : check 4000 c2531 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2532 : RawOriginal := C019.records[100]'(by decide)
theorem original_id2532 : original2532.index = 2532 := by decide

def c2532 : Contract := original2532.toContract.get (by decide)
theorem binding2532 : original2532.toContract = some c2532 := rfl

theorem checked2532 : check 4000 c2532 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2533 : RawOriginal := C019.records[101]'(by decide)
theorem original_id2533 : original2533.index = 2533 := by decide

def c2533 : Contract := original2533.toContract.get (by decide)
theorem binding2533 : original2533.toContract = some c2533 := rfl

theorem checked2533 : check 4000 c2533 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2518, c2518, 4000, checked2518⟩,
  ⟨2519, c2519, 4000, checked2519⟩,
  ⟨2520, c2520, 4000, checked2520⟩,
  ⟨2521, c2521, 4000, checked2521⟩,
  ⟨2522, c2522, 4000, checked2522⟩,
  ⟨2523, c2523, 4000, checked2523⟩,
  ⟨2524, c2524, 4000, checked2524⟩,
  ⟨2525, c2525, 4000, checked2525⟩,
  ⟨2526, c2526, 4000, checked2526⟩,
  ⟨2527, c2527, 4000, checked2527⟩,
  ⟨2528, c2528, 4000, checked2528⟩,
  ⟨2529, c2529, 4000, checked2529⟩,
  ⟨2530, c2530, 4000, checked2530⟩,
  ⟨2531, c2531, 4000, checked2531⟩,
  ⟨2532, c2532, 4000, checked2532⟩,
  ⟨2533, c2533, 4000, checked2533⟩]

end PA215.ContractShards.Shard019Part5
