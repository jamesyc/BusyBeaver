import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C019
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard019Part2
open PA215.Contracts PA215.Census

def original2470 : RawOriginal := C019.records[38]'(by decide)
theorem original_id2470 : original2470.index = 2470 := by decide

def c2470 : Contract := original2470.toContract.get (by decide)
theorem binding2470 : original2470.toContract = some c2470 := rfl

theorem checked2470 : check 4000 c2470 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2471 : RawOriginal := C019.records[39]'(by decide)
theorem original_id2471 : original2471.index = 2471 := by decide

def c2471 : Contract := original2471.toContract.get (by decide)
theorem binding2471 : original2471.toContract = some c2471 := rfl

theorem checked2471 : check 4000 c2471 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2472 : RawOriginal := C019.records[40]'(by decide)
theorem original_id2472 : original2472.index = 2472 := by decide

def c2472 : Contract := original2472.toContract.get (by decide)
theorem binding2472 : original2472.toContract = some c2472 := rfl

theorem checked2472 : check 4000 c2472 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2473 : RawOriginal := C019.records[41]'(by decide)
theorem original_id2473 : original2473.index = 2473 := by decide

def c2473 : Contract := original2473.toContract.get (by decide)
theorem binding2473 : original2473.toContract = some c2473 := rfl

theorem checked2473 : check 4000 c2473 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2474 : RawOriginal := C019.records[42]'(by decide)
theorem original_id2474 : original2474.index = 2474 := by decide

def c2474 : Contract := original2474.toContract.get (by decide)
theorem binding2474 : original2474.toContract = some c2474 := rfl

theorem checked2474 : check 4000 c2474 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2475 : RawOriginal := C019.records[43]'(by decide)
theorem original_id2475 : original2475.index = 2475 := by decide

def c2475 : Contract := original2475.toContract.get (by decide)
theorem binding2475 : original2475.toContract = some c2475 := rfl

theorem checked2475 : check 4000 c2475 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2476 : RawOriginal := C019.records[44]'(by decide)
theorem original_id2476 : original2476.index = 2476 := by decide

def c2476 : Contract := original2476.toContract.get (by decide)
theorem binding2476 : original2476.toContract = some c2476 := rfl

theorem checked2476 : check 4000 c2476 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2477 : RawOriginal := C019.records[45]'(by decide)
theorem original_id2477 : original2477.index = 2477 := by decide

def c2477 : Contract := original2477.toContract.get (by decide)
theorem binding2477 : original2477.toContract = some c2477 := rfl

theorem checked2477 : check 4000 c2477 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2478 : RawOriginal := C019.records[46]'(by decide)
theorem original_id2478 : original2478.index = 2478 := by decide

def c2478 : Contract := original2478.toContract.get (by decide)
theorem binding2478 : original2478.toContract = some c2478 := rfl

theorem checked2478 : check 4000 c2478 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2479 : RawOriginal := C019.records[47]'(by decide)
theorem original_id2479 : original2479.index = 2479 := by decide

def c2479 : Contract := original2479.toContract.get (by decide)
theorem binding2479 : original2479.toContract = some c2479 := rfl

theorem checked2479 : check 4000 c2479 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2480 : RawOriginal := C019.records[48]'(by decide)
theorem original_id2480 : original2480.index = 2480 := by decide

def c2480 : Contract := original2480.toContract.get (by decide)
theorem binding2480 : original2480.toContract = some c2480 := rfl

theorem checked2480 : check 4000 c2480 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2481 : RawOriginal := C019.records[49]'(by decide)
theorem original_id2481 : original2481.index = 2481 := by decide

def c2481 : Contract := original2481.toContract.get (by decide)
theorem binding2481 : original2481.toContract = some c2481 := rfl

theorem checked2481 : check 4000 c2481 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2482 : RawOriginal := C019.records[50]'(by decide)
theorem original_id2482 : original2482.index = 2482 := by decide

def c2482 : Contract := original2482.toContract.get (by decide)
theorem binding2482 : original2482.toContract = some c2482 := rfl

theorem checked2482 : check 4000 c2482 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2483 : RawOriginal := C019.records[51]'(by decide)
theorem original_id2483 : original2483.index = 2483 := by decide

def c2483 : Contract := original2483.toContract.get (by decide)
theorem binding2483 : original2483.toContract = some c2483 := rfl

theorem checked2483 : check 4000 c2483 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2484 : RawOriginal := C019.records[52]'(by decide)
theorem original_id2484 : original2484.index = 2484 := by decide

def c2484 : Contract := original2484.toContract.get (by decide)
theorem binding2484 : original2484.toContract = some c2484 := rfl

theorem checked2484 : check 4000 c2484 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2485 : RawOriginal := C019.records[53]'(by decide)
theorem original_id2485 : original2485.index = 2485 := by decide

def c2485 : Contract := original2485.toContract.get (by decide)
theorem binding2485 : original2485.toContract = some c2485 := rfl

theorem checked2485 : check 4000 c2485 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2470, c2470, 4000, checked2470⟩,
  ⟨2471, c2471, 4000, checked2471⟩,
  ⟨2472, c2472, 4000, checked2472⟩,
  ⟨2473, c2473, 4000, checked2473⟩,
  ⟨2474, c2474, 4000, checked2474⟩,
  ⟨2475, c2475, 4000, checked2475⟩,
  ⟨2476, c2476, 4000, checked2476⟩,
  ⟨2477, c2477, 4000, checked2477⟩,
  ⟨2478, c2478, 4000, checked2478⟩,
  ⟨2479, c2479, 4000, checked2479⟩,
  ⟨2480, c2480, 4000, checked2480⟩,
  ⟨2481, c2481, 4000, checked2481⟩,
  ⟨2482, c2482, 4000, checked2482⟩,
  ⟨2483, c2483, 4000, checked2483⟩,
  ⟨2484, c2484, 4000, checked2484⟩,
  ⟨2485, c2485, 4000, checked2485⟩]

end PA215.ContractShards.Shard019Part2
