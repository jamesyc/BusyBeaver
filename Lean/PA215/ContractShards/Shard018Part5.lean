import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C018
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard018Part5
open PA215.Contracts PA215.Census

def original2390 : RawOriginal := C018.records[86]'(by decide)
theorem original_id2390 : original2390.index = 2390 := by decide

def c2390 : Contract := original2390.toContract.get (by decide)
theorem binding2390 : original2390.toContract = some c2390 := rfl

theorem checked2390 : check 4000 c2390 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2391 : RawOriginal := C018.records[87]'(by decide)
theorem original_id2391 : original2391.index = 2391 := by decide

def c2391 : Contract := original2391.toContract.get (by decide)
theorem binding2391 : original2391.toContract = some c2391 := rfl

theorem checked2391 : check 4000 c2391 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2392 : RawOriginal := C018.records[88]'(by decide)
theorem original_id2392 : original2392.index = 2392 := by decide

def c2392 : Contract := original2392.toContract.get (by decide)
theorem binding2392 : original2392.toContract = some c2392 := rfl

theorem checked2392 : check 4000 c2392 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2393 : RawOriginal := C018.records[89]'(by decide)
theorem original_id2393 : original2393.index = 2393 := by decide

def c2393 : Contract := original2393.toContract.get (by decide)
theorem binding2393 : original2393.toContract = some c2393 := rfl

theorem checked2393 : check 4000 c2393 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2394 : RawOriginal := C018.records[90]'(by decide)
theorem original_id2394 : original2394.index = 2394 := by decide

def c2394 : Contract := original2394.toContract.get (by decide)
theorem binding2394 : original2394.toContract = some c2394 := rfl

theorem checked2394 : check 4000 c2394 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2395 : RawOriginal := C018.records[91]'(by decide)
theorem original_id2395 : original2395.index = 2395 := by decide

def c2395 : Contract := original2395.toContract.get (by decide)
theorem binding2395 : original2395.toContract = some c2395 := rfl

theorem checked2395 : check 4000 c2395 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2396 : RawOriginal := C018.records[92]'(by decide)
theorem original_id2396 : original2396.index = 2396 := by decide

def c2396 : Contract := original2396.toContract.get (by decide)
theorem binding2396 : original2396.toContract = some c2396 := rfl

theorem checked2396 : check 4000 c2396 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2397 : RawOriginal := C018.records[93]'(by decide)
theorem original_id2397 : original2397.index = 2397 := by decide

def c2397 : Contract := original2397.toContract.get (by decide)
theorem binding2397 : original2397.toContract = some c2397 := rfl

theorem checked2397 : check 4000 c2397 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2398 : RawOriginal := C018.records[94]'(by decide)
theorem original_id2398 : original2398.index = 2398 := by decide

def c2398 : Contract := original2398.toContract.get (by decide)
theorem binding2398 : original2398.toContract = some c2398 := rfl

theorem checked2398 : check 4000 c2398 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2399 : RawOriginal := C018.records[95]'(by decide)
theorem original_id2399 : original2399.index = 2399 := by decide

def c2399 : Contract := original2399.toContract.get (by decide)
theorem binding2399 : original2399.toContract = some c2399 := rfl

theorem checked2399 : check 4000 c2399 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2400 : RawOriginal := C018.records[96]'(by decide)
theorem original_id2400 : original2400.index = 2400 := by decide

def c2400 : Contract := original2400.toContract.get (by decide)
theorem binding2400 : original2400.toContract = some c2400 := rfl

theorem checked2400 : check 4000 c2400 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2401 : RawOriginal := C018.records[97]'(by decide)
theorem original_id2401 : original2401.index = 2401 := by decide

def c2401 : Contract := original2401.toContract.get (by decide)
theorem binding2401 : original2401.toContract = some c2401 := rfl

theorem checked2401 : check 4000 c2401 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2402 : RawOriginal := C018.records[98]'(by decide)
theorem original_id2402 : original2402.index = 2402 := by decide

def c2402 : Contract := original2402.toContract.get (by decide)
theorem binding2402 : original2402.toContract = some c2402 := rfl

theorem checked2402 : check 4000 c2402 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2403 : RawOriginal := C018.records[99]'(by decide)
theorem original_id2403 : original2403.index = 2403 := by decide

def c2403 : Contract := original2403.toContract.get (by decide)
theorem binding2403 : original2403.toContract = some c2403 := rfl

theorem checked2403 : check 4000 c2403 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2404 : RawOriginal := C018.records[100]'(by decide)
theorem original_id2404 : original2404.index = 2404 := by decide

def c2404 : Contract := original2404.toContract.get (by decide)
theorem binding2404 : original2404.toContract = some c2404 := rfl

theorem checked2404 : check 4000 c2404 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2405 : RawOriginal := C018.records[101]'(by decide)
theorem original_id2405 : original2405.index = 2405 := by decide

def c2405 : Contract := original2405.toContract.get (by decide)
theorem binding2405 : original2405.toContract = some c2405 := rfl

theorem checked2405 : check 4000 c2405 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2390, c2390, 4000, checked2390⟩,
  ⟨2391, c2391, 4000, checked2391⟩,
  ⟨2392, c2392, 4000, checked2392⟩,
  ⟨2393, c2393, 4000, checked2393⟩,
  ⟨2394, c2394, 4000, checked2394⟩,
  ⟨2395, c2395, 4000, checked2395⟩,
  ⟨2396, c2396, 4000, checked2396⟩,
  ⟨2397, c2397, 4000, checked2397⟩,
  ⟨2398, c2398, 4000, checked2398⟩,
  ⟨2399, c2399, 4000, checked2399⟩,
  ⟨2400, c2400, 4000, checked2400⟩,
  ⟨2401, c2401, 4000, checked2401⟩,
  ⟨2402, c2402, 4000, checked2402⟩,
  ⟨2403, c2403, 4000, checked2403⟩,
  ⟨2404, c2404, 4000, checked2404⟩,
  ⟨2405, c2405, 4000, checked2405⟩]

end PA215.ContractShards.Shard018Part5
