import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C019
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard019Part4
open PA215.Contracts PA215.Census

def original2502 : RawOriginal := C019.records[70]'(by decide)
theorem original_id2502 : original2502.index = 2502 := by decide

def c2502 : Contract := original2502.toContract.get (by decide)
theorem binding2502 : original2502.toContract = some c2502 := rfl

theorem checked2502 : check 4000 c2502 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2503 : RawOriginal := C019.records[71]'(by decide)
theorem original_id2503 : original2503.index = 2503 := by decide

def c2503 : Contract := original2503.toContract.get (by decide)
theorem binding2503 : original2503.toContract = some c2503 := rfl

theorem checked2503 : check 4000 c2503 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2504 : RawOriginal := C019.records[72]'(by decide)
theorem original_id2504 : original2504.index = 2504 := by decide

def c2504 : Contract := original2504.toContract.get (by decide)
theorem binding2504 : original2504.toContract = some c2504 := rfl

theorem checked2504 : check 4000 c2504 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2505 : RawOriginal := C019.records[73]'(by decide)
theorem original_id2505 : original2505.index = 2505 := by decide

def c2505 : Contract := original2505.toContract.get (by decide)
theorem binding2505 : original2505.toContract = some c2505 := rfl

theorem checked2505 : check 4000 c2505 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2506 : RawOriginal := C019.records[74]'(by decide)
theorem original_id2506 : original2506.index = 2506 := by decide

def c2506 : Contract := original2506.toContract.get (by decide)
theorem binding2506 : original2506.toContract = some c2506 := rfl

theorem checked2506 : check 4000 c2506 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2507 : RawOriginal := C019.records[75]'(by decide)
theorem original_id2507 : original2507.index = 2507 := by decide

def c2507 : Contract := original2507.toContract.get (by decide)
theorem binding2507 : original2507.toContract = some c2507 := rfl

theorem checked2507 : check 4000 c2507 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2508 : RawOriginal := C019.records[76]'(by decide)
theorem original_id2508 : original2508.index = 2508 := by decide

def c2508 : Contract := original2508.toContract.get (by decide)
theorem binding2508 : original2508.toContract = some c2508 := rfl

theorem checked2508 : check 4000 c2508 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2509 : RawOriginal := C019.records[77]'(by decide)
theorem original_id2509 : original2509.index = 2509 := by decide

def c2509 : Contract := original2509.toContract.get (by decide)
theorem binding2509 : original2509.toContract = some c2509 := rfl

theorem checked2509 : check 4000 c2509 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2510 : RawOriginal := C019.records[78]'(by decide)
theorem original_id2510 : original2510.index = 2510 := by decide

def c2510 : Contract := original2510.toContract.get (by decide)
theorem binding2510 : original2510.toContract = some c2510 := rfl

theorem checked2510 : check 4000 c2510 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2511 : RawOriginal := C019.records[79]'(by decide)
theorem original_id2511 : original2511.index = 2511 := by decide

def c2511 : Contract := original2511.toContract.get (by decide)
theorem binding2511 : original2511.toContract = some c2511 := rfl

theorem checked2511 : check 4000 c2511 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2512 : RawOriginal := C019.records[80]'(by decide)
theorem original_id2512 : original2512.index = 2512 := by decide

def c2512 : Contract := original2512.toContract.get (by decide)
theorem binding2512 : original2512.toContract = some c2512 := rfl

theorem checked2512 : check 4000 c2512 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2513 : RawOriginal := C019.records[81]'(by decide)
theorem original_id2513 : original2513.index = 2513 := by decide

def c2513 : Contract := original2513.toContract.get (by decide)
theorem binding2513 : original2513.toContract = some c2513 := rfl

theorem checked2513 : check 4000 c2513 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2514 : RawOriginal := C019.records[82]'(by decide)
theorem original_id2514 : original2514.index = 2514 := by decide

def c2514 : Contract := original2514.toContract.get (by decide)
theorem binding2514 : original2514.toContract = some c2514 := rfl

theorem checked2514 : check 4000 c2514 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2515 : RawOriginal := C019.records[83]'(by decide)
theorem original_id2515 : original2515.index = 2515 := by decide

def c2515 : Contract := original2515.toContract.get (by decide)
theorem binding2515 : original2515.toContract = some c2515 := rfl

theorem checked2515 : check 4000 c2515 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2516 : RawOriginal := C019.records[84]'(by decide)
theorem original_id2516 : original2516.index = 2516 := by decide

def c2516 : Contract := original2516.toContract.get (by decide)
theorem binding2516 : original2516.toContract = some c2516 := rfl

theorem checked2516 : check 4000 c2516 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2517 : RawOriginal := C019.records[85]'(by decide)
theorem original_id2517 : original2517.index = 2517 := by decide

def c2517 : Contract := original2517.toContract.get (by decide)
theorem binding2517 : original2517.toContract = some c2517 := rfl

theorem checked2517 : check 4000 c2517 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2502, c2502, 4000, checked2502⟩,
  ⟨2503, c2503, 4000, checked2503⟩,
  ⟨2504, c2504, 4000, checked2504⟩,
  ⟨2505, c2505, 4000, checked2505⟩,
  ⟨2506, c2506, 4000, checked2506⟩,
  ⟨2507, c2507, 4000, checked2507⟩,
  ⟨2508, c2508, 4000, checked2508⟩,
  ⟨2509, c2509, 4000, checked2509⟩,
  ⟨2510, c2510, 4000, checked2510⟩,
  ⟨2511, c2511, 4000, checked2511⟩,
  ⟨2512, c2512, 4000, checked2512⟩,
  ⟨2513, c2513, 4000, checked2513⟩,
  ⟨2514, c2514, 4000, checked2514⟩,
  ⟨2515, c2515, 4000, checked2515⟩,
  ⟨2516, c2516, 4000, checked2516⟩,
  ⟨2517, c2517, 4000, checked2517⟩]

end PA215.ContractShards.Shard019Part4
