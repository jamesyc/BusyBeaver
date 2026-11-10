import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C019
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard019Part0
open PA215.Contracts PA215.Census

def original2438 : RawOriginal := C019.records[6]'(by decide)
theorem original_id2438 : original2438.index = 2438 := by decide

def c2438 : Contract := original2438.toContract.get (by decide)
theorem binding2438 : original2438.toContract = some c2438 := rfl

theorem checked2438 : check 4000 c2438 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2439 : RawOriginal := C019.records[7]'(by decide)
theorem original_id2439 : original2439.index = 2439 := by decide

def c2439 : Contract := original2439.toContract.get (by decide)
theorem binding2439 : original2439.toContract = some c2439 := rfl

theorem checked2439 : check 4000 c2439 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2440 : RawOriginal := C019.records[8]'(by decide)
theorem original_id2440 : original2440.index = 2440 := by decide

def c2440 : Contract := original2440.toContract.get (by decide)
theorem binding2440 : original2440.toContract = some c2440 := rfl

theorem checked2440 : check 4000 c2440 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2441 : RawOriginal := C019.records[9]'(by decide)
theorem original_id2441 : original2441.index = 2441 := by decide

def c2441 : Contract := original2441.toContract.get (by decide)
theorem binding2441 : original2441.toContract = some c2441 := rfl

theorem checked2441 : check 4000 c2441 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2442 : RawOriginal := C019.records[10]'(by decide)
theorem original_id2442 : original2442.index = 2442 := by decide

def c2442 : Contract := original2442.toContract.get (by decide)
theorem binding2442 : original2442.toContract = some c2442 := rfl

theorem checked2442 : check 4000 c2442 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2443 : RawOriginal := C019.records[11]'(by decide)
theorem original_id2443 : original2443.index = 2443 := by decide

def c2443 : Contract := original2443.toContract.get (by decide)
theorem binding2443 : original2443.toContract = some c2443 := rfl

theorem checked2443 : check 4000 c2443 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2444 : RawOriginal := C019.records[12]'(by decide)
theorem original_id2444 : original2444.index = 2444 := by decide

def c2444 : Contract := original2444.toContract.get (by decide)
theorem binding2444 : original2444.toContract = some c2444 := rfl

theorem checked2444 : check 4000 c2444 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2445 : RawOriginal := C019.records[13]'(by decide)
theorem original_id2445 : original2445.index = 2445 := by decide

def c2445 : Contract := original2445.toContract.get (by decide)
theorem binding2445 : original2445.toContract = some c2445 := rfl

theorem checked2445 : check 4000 c2445 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2446 : RawOriginal := C019.records[14]'(by decide)
theorem original_id2446 : original2446.index = 2446 := by decide

def c2446 : Contract := original2446.toContract.get (by decide)
theorem binding2446 : original2446.toContract = some c2446 := rfl

theorem checked2446 : check 4000 c2446 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2447 : RawOriginal := C019.records[15]'(by decide)
theorem original_id2447 : original2447.index = 2447 := by decide

def c2447 : Contract := original2447.toContract.get (by decide)
theorem binding2447 : original2447.toContract = some c2447 := rfl

theorem checked2447 : check 4000 c2447 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2448 : RawOriginal := C019.records[16]'(by decide)
theorem original_id2448 : original2448.index = 2448 := by decide

def c2448 : Contract := original2448.toContract.get (by decide)
theorem binding2448 : original2448.toContract = some c2448 := rfl

theorem checked2448 : check 4000 c2448 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2449 : RawOriginal := C019.records[17]'(by decide)
theorem original_id2449 : original2449.index = 2449 := by decide

def c2449 : Contract := original2449.toContract.get (by decide)
theorem binding2449 : original2449.toContract = some c2449 := rfl

theorem checked2449 : check 4000 c2449 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2450 : RawOriginal := C019.records[18]'(by decide)
theorem original_id2450 : original2450.index = 2450 := by decide

def c2450 : Contract := original2450.toContract.get (by decide)
theorem binding2450 : original2450.toContract = some c2450 := rfl

theorem checked2450 : check 4000 c2450 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2451 : RawOriginal := C019.records[19]'(by decide)
theorem original_id2451 : original2451.index = 2451 := by decide

def c2451 : Contract := original2451.toContract.get (by decide)
theorem binding2451 : original2451.toContract = some c2451 := rfl

theorem checked2451 : check 4000 c2451 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2452 : RawOriginal := C019.records[20]'(by decide)
theorem original_id2452 : original2452.index = 2452 := by decide

def c2452 : Contract := original2452.toContract.get (by decide)
theorem binding2452 : original2452.toContract = some c2452 := rfl

theorem checked2452 : check 4000 c2452 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2453 : RawOriginal := C019.records[21]'(by decide)
theorem original_id2453 : original2453.index = 2453 := by decide

def c2453 : Contract := original2453.toContract.get (by decide)
theorem binding2453 : original2453.toContract = some c2453 := rfl

theorem checked2453 : check 4000 c2453 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2438, c2438, 4000, checked2438⟩,
  ⟨2439, c2439, 4000, checked2439⟩,
  ⟨2440, c2440, 4000, checked2440⟩,
  ⟨2441, c2441, 4000, checked2441⟩,
  ⟨2442, c2442, 4000, checked2442⟩,
  ⟨2443, c2443, 4000, checked2443⟩,
  ⟨2444, c2444, 4000, checked2444⟩,
  ⟨2445, c2445, 4000, checked2445⟩,
  ⟨2446, c2446, 4000, checked2446⟩,
  ⟨2447, c2447, 4000, checked2447⟩,
  ⟨2448, c2448, 4000, checked2448⟩,
  ⟨2449, c2449, 4000, checked2449⟩,
  ⟨2450, c2450, 4000, checked2450⟩,
  ⟨2451, c2451, 4000, checked2451⟩,
  ⟨2452, c2452, 4000, checked2452⟩,
  ⟨2453, c2453, 4000, checked2453⟩]

end PA215.ContractShards.Shard019Part0
