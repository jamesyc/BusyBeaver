import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C019
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard019Part1
open PA215.Contracts PA215.Census

def original2454 : RawOriginal := C019.records[22]'(by decide)
theorem original_id2454 : original2454.index = 2454 := by decide

def c2454 : Contract := original2454.toContract.get (by decide)
theorem binding2454 : original2454.toContract = some c2454 := rfl

theorem checked2454 : check 4000 c2454 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2455 : RawOriginal := C019.records[23]'(by decide)
theorem original_id2455 : original2455.index = 2455 := by decide

def c2455 : Contract := original2455.toContract.get (by decide)
theorem binding2455 : original2455.toContract = some c2455 := rfl

theorem checked2455 : check 4000 c2455 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2456 : RawOriginal := C019.records[24]'(by decide)
theorem original_id2456 : original2456.index = 2456 := by decide

def c2456 : Contract := original2456.toContract.get (by decide)
theorem binding2456 : original2456.toContract = some c2456 := rfl

theorem checked2456 : check 4000 c2456 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2457 : RawOriginal := C019.records[25]'(by decide)
theorem original_id2457 : original2457.index = 2457 := by decide

def c2457 : Contract := original2457.toContract.get (by decide)
theorem binding2457 : original2457.toContract = some c2457 := rfl

theorem checked2457 : check 4000 c2457 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2458 : RawOriginal := C019.records[26]'(by decide)
theorem original_id2458 : original2458.index = 2458 := by decide

def c2458 : Contract := original2458.toContract.get (by decide)
theorem binding2458 : original2458.toContract = some c2458 := rfl

theorem checked2458 : check 4000 c2458 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2459 : RawOriginal := C019.records[27]'(by decide)
theorem original_id2459 : original2459.index = 2459 := by decide

def c2459 : Contract := original2459.toContract.get (by decide)
theorem binding2459 : original2459.toContract = some c2459 := rfl

theorem checked2459 : check 4000 c2459 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2460 : RawOriginal := C019.records[28]'(by decide)
theorem original_id2460 : original2460.index = 2460 := by decide

def c2460 : Contract := original2460.toContract.get (by decide)
theorem binding2460 : original2460.toContract = some c2460 := rfl

theorem checked2460 : check 4000 c2460 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2461 : RawOriginal := C019.records[29]'(by decide)
theorem original_id2461 : original2461.index = 2461 := by decide

def c2461 : Contract := original2461.toContract.get (by decide)
theorem binding2461 : original2461.toContract = some c2461 := rfl

theorem checked2461 : check 4000 c2461 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2462 : RawOriginal := C019.records[30]'(by decide)
theorem original_id2462 : original2462.index = 2462 := by decide

def c2462 : Contract := original2462.toContract.get (by decide)
theorem binding2462 : original2462.toContract = some c2462 := rfl

theorem checked2462 : check 4000 c2462 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2463 : RawOriginal := C019.records[31]'(by decide)
theorem original_id2463 : original2463.index = 2463 := by decide

def c2463 : Contract := original2463.toContract.get (by decide)
theorem binding2463 : original2463.toContract = some c2463 := rfl

theorem checked2463 : check 4000 c2463 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2464 : RawOriginal := C019.records[32]'(by decide)
theorem original_id2464 : original2464.index = 2464 := by decide

def c2464 : Contract := original2464.toContract.get (by decide)
theorem binding2464 : original2464.toContract = some c2464 := rfl

theorem checked2464 : check 4000 c2464 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2465 : RawOriginal := C019.records[33]'(by decide)
theorem original_id2465 : original2465.index = 2465 := by decide

def c2465 : Contract := original2465.toContract.get (by decide)
theorem binding2465 : original2465.toContract = some c2465 := rfl

theorem checked2465 : check 4000 c2465 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2466 : RawOriginal := C019.records[34]'(by decide)
theorem original_id2466 : original2466.index = 2466 := by decide

def c2466 : Contract := original2466.toContract.get (by decide)
theorem binding2466 : original2466.toContract = some c2466 := rfl

theorem checked2466 : check 4000 c2466 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2467 : RawOriginal := C019.records[35]'(by decide)
theorem original_id2467 : original2467.index = 2467 := by decide

def c2467 : Contract := original2467.toContract.get (by decide)
theorem binding2467 : original2467.toContract = some c2467 := rfl

theorem checked2467 : check 4000 c2467 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2468 : RawOriginal := C019.records[36]'(by decide)
theorem original_id2468 : original2468.index = 2468 := by decide

def c2468 : Contract := original2468.toContract.get (by decide)
theorem binding2468 : original2468.toContract = some c2468 := rfl

theorem checked2468 : check 4000 c2468 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2469 : RawOriginal := C019.records[37]'(by decide)
theorem original_id2469 : original2469.index = 2469 := by decide

def c2469 : Contract := original2469.toContract.get (by decide)
theorem binding2469 : original2469.toContract = some c2469 := rfl

theorem checked2469 : check 4000 c2469 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2454, c2454, 4000, checked2454⟩,
  ⟨2455, c2455, 4000, checked2455⟩,
  ⟨2456, c2456, 4000, checked2456⟩,
  ⟨2457, c2457, 4000, checked2457⟩,
  ⟨2458, c2458, 4000, checked2458⟩,
  ⟨2459, c2459, 4000, checked2459⟩,
  ⟨2460, c2460, 4000, checked2460⟩,
  ⟨2461, c2461, 4000, checked2461⟩,
  ⟨2462, c2462, 4000, checked2462⟩,
  ⟨2463, c2463, 4000, checked2463⟩,
  ⟨2464, c2464, 4000, checked2464⟩,
  ⟨2465, c2465, 4000, checked2465⟩,
  ⟨2466, c2466, 4000, checked2466⟩,
  ⟨2467, c2467, 4000, checked2467⟩,
  ⟨2468, c2468, 4000, checked2468⟩,
  ⟨2469, c2469, 4000, checked2469⟩]

end PA215.ContractShards.Shard019Part1
