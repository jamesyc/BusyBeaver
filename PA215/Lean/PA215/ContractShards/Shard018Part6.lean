import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C018
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard018Part6
open PA215.Contracts PA215.Census

def original2406 : RawOriginal := C018.records[102]'(by decide)
theorem original_id2406 : original2406.index = 2406 := by decide

def c2406 : Contract := original2406.toContract.get (by decide)
theorem binding2406 : original2406.toContract = some c2406 := rfl

theorem checked2406 : check 4000 c2406 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2407 : RawOriginal := C018.records[103]'(by decide)
theorem original_id2407 : original2407.index = 2407 := by decide

def c2407 : Contract := original2407.toContract.get (by decide)
theorem binding2407 : original2407.toContract = some c2407 := rfl

theorem checked2407 : check 4000 c2407 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2408 : RawOriginal := C018.records[104]'(by decide)
theorem original_id2408 : original2408.index = 2408 := by decide

def c2408 : Contract := original2408.toContract.get (by decide)
theorem binding2408 : original2408.toContract = some c2408 := rfl

theorem checked2408 : check 4000 c2408 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2409 : RawOriginal := C018.records[105]'(by decide)
theorem original_id2409 : original2409.index = 2409 := by decide

def c2409 : Contract := original2409.toContract.get (by decide)
theorem binding2409 : original2409.toContract = some c2409 := rfl

theorem checked2409 : check 4000 c2409 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2410 : RawOriginal := C018.records[106]'(by decide)
theorem original_id2410 : original2410.index = 2410 := by decide

def c2410 : Contract := original2410.toContract.get (by decide)
theorem binding2410 : original2410.toContract = some c2410 := rfl

theorem checked2410 : check 4000 c2410 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2411 : RawOriginal := C018.records[107]'(by decide)
theorem original_id2411 : original2411.index = 2411 := by decide

def c2411 : Contract := original2411.toContract.get (by decide)
theorem binding2411 : original2411.toContract = some c2411 := rfl

theorem checked2411 : check 4000 c2411 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2412 : RawOriginal := C018.records[108]'(by decide)
theorem original_id2412 : original2412.index = 2412 := by decide

def c2412 : Contract := original2412.toContract.get (by decide)
theorem binding2412 : original2412.toContract = some c2412 := rfl

theorem checked2412 : check 4000 c2412 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2413 : RawOriginal := C018.records[109]'(by decide)
theorem original_id2413 : original2413.index = 2413 := by decide

def c2413 : Contract := original2413.toContract.get (by decide)
theorem binding2413 : original2413.toContract = some c2413 := rfl

theorem checked2413 : check 4000 c2413 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2414 : RawOriginal := C018.records[110]'(by decide)
theorem original_id2414 : original2414.index = 2414 := by decide

def c2414 : Contract := original2414.toContract.get (by decide)
theorem binding2414 : original2414.toContract = some c2414 := rfl

theorem checked2414 : check 4000 c2414 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2415 : RawOriginal := C018.records[111]'(by decide)
theorem original_id2415 : original2415.index = 2415 := by decide

def c2415 : Contract := original2415.toContract.get (by decide)
theorem binding2415 : original2415.toContract = some c2415 := rfl

theorem checked2415 : check 4000 c2415 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2416 : RawOriginal := C018.records[112]'(by decide)
theorem original_id2416 : original2416.index = 2416 := by decide

def c2416 : Contract := original2416.toContract.get (by decide)
theorem binding2416 : original2416.toContract = some c2416 := rfl

theorem checked2416 : check 4000 c2416 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2417 : RawOriginal := C018.records[113]'(by decide)
theorem original_id2417 : original2417.index = 2417 := by decide

def c2417 : Contract := original2417.toContract.get (by decide)
theorem binding2417 : original2417.toContract = some c2417 := rfl

theorem checked2417 : check 4000 c2417 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2418 : RawOriginal := C018.records[114]'(by decide)
theorem original_id2418 : original2418.index = 2418 := by decide

def c2418 : Contract := original2418.toContract.get (by decide)
theorem binding2418 : original2418.toContract = some c2418 := rfl

theorem checked2418 : check 4000 c2418 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2419 : RawOriginal := C018.records[115]'(by decide)
theorem original_id2419 : original2419.index = 2419 := by decide

def c2419 : Contract := original2419.toContract.get (by decide)
theorem binding2419 : original2419.toContract = some c2419 := rfl

theorem checked2419 : check 4000 c2419 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2420 : RawOriginal := C018.records[116]'(by decide)
theorem original_id2420 : original2420.index = 2420 := by decide

def c2420 : Contract := original2420.toContract.get (by decide)
theorem binding2420 : original2420.toContract = some c2420 := rfl

theorem checked2420 : check 4000 c2420 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2421 : RawOriginal := C018.records[117]'(by decide)
theorem original_id2421 : original2421.index = 2421 := by decide

def c2421 : Contract := original2421.toContract.get (by decide)
theorem binding2421 : original2421.toContract = some c2421 := rfl

theorem checked2421 : check 4000 c2421 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2406, c2406, 4000, checked2406⟩,
  ⟨2407, c2407, 4000, checked2407⟩,
  ⟨2408, c2408, 4000, checked2408⟩,
  ⟨2409, c2409, 4000, checked2409⟩,
  ⟨2410, c2410, 4000, checked2410⟩,
  ⟨2411, c2411, 4000, checked2411⟩,
  ⟨2412, c2412, 4000, checked2412⟩,
  ⟨2413, c2413, 4000, checked2413⟩,
  ⟨2414, c2414, 4000, checked2414⟩,
  ⟨2415, c2415, 4000, checked2415⟩,
  ⟨2416, c2416, 4000, checked2416⟩,
  ⟨2417, c2417, 4000, checked2417⟩,
  ⟨2418, c2418, 4000, checked2418⟩,
  ⟨2419, c2419, 4000, checked2419⟩,
  ⟨2420, c2420, 4000, checked2420⟩,
  ⟨2421, c2421, 4000, checked2421⟩]

end PA215.ContractShards.Shard018Part6
