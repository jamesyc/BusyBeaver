import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C018
import PA215.Census.C019
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard018Part7
open PA215.Contracts PA215.Census

def original2422 : RawOriginal := C018.records[118]'(by decide)
theorem original_id2422 : original2422.index = 2422 := by decide

def c2422 : Contract := original2422.toContract.get (by decide)
theorem binding2422 : original2422.toContract = some c2422 := rfl

theorem checked2422 : check 4000 c2422 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2423 : RawOriginal := C018.records[119]'(by decide)
theorem original_id2423 : original2423.index = 2423 := by decide

def c2423 : Contract := original2423.toContract.get (by decide)
theorem binding2423 : original2423.toContract = some c2423 := rfl

theorem checked2423 : check 4000 c2423 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2424 : RawOriginal := C018.records[120]'(by decide)
theorem original_id2424 : original2424.index = 2424 := by decide

def c2424 : Contract := original2424.toContract.get (by decide)
theorem binding2424 : original2424.toContract = some c2424 := rfl

theorem checked2424 : check 4000 c2424 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2425 : RawOriginal := C018.records[121]'(by decide)
theorem original_id2425 : original2425.index = 2425 := by decide

def c2425 : Contract := original2425.toContract.get (by decide)
theorem binding2425 : original2425.toContract = some c2425 := rfl

theorem checked2425 : check 4000 c2425 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2426 : RawOriginal := C018.records[122]'(by decide)
theorem original_id2426 : original2426.index = 2426 := by decide

def c2426 : Contract := original2426.toContract.get (by decide)
theorem binding2426 : original2426.toContract = some c2426 := rfl

theorem checked2426 : check 4000 c2426 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2427 : RawOriginal := C018.records[123]'(by decide)
theorem original_id2427 : original2427.index = 2427 := by decide

def c2427 : Contract := original2427.toContract.get (by decide)
theorem binding2427 : original2427.toContract = some c2427 := rfl

theorem checked2427 : check 4000 c2427 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2428 : RawOriginal := C018.records[124]'(by decide)
theorem original_id2428 : original2428.index = 2428 := by decide

def c2428 : Contract := original2428.toContract.get (by decide)
theorem binding2428 : original2428.toContract = some c2428 := rfl

theorem checked2428 : check 4000 c2428 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2429 : RawOriginal := C018.records[125]'(by decide)
theorem original_id2429 : original2429.index = 2429 := by decide

def c2429 : Contract := original2429.toContract.get (by decide)
theorem binding2429 : original2429.toContract = some c2429 := rfl

theorem checked2429 : check 4000 c2429 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2430 : RawOriginal := C018.records[126]'(by decide)
theorem original_id2430 : original2430.index = 2430 := by decide

def c2430 : Contract := original2430.toContract.get (by decide)
theorem binding2430 : original2430.toContract = some c2430 := rfl

theorem checked2430 : check 4000 c2430 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2431 : RawOriginal := C018.records[127]'(by decide)
theorem original_id2431 : original2431.index = 2431 := by decide

def c2431 : Contract := original2431.toContract.get (by decide)
theorem binding2431 : original2431.toContract = some c2431 := rfl

theorem checked2431 : check 4000 c2431 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2432 : RawOriginal := C019.records[0]'(by decide)
theorem original_id2432 : original2432.index = 2432 := by decide

def c2432 : Contract := original2432.toContract.get (by decide)
theorem binding2432 : original2432.toContract = some c2432 := rfl

theorem checked2432 : check 4000 c2432 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2433 : RawOriginal := C019.records[1]'(by decide)
theorem original_id2433 : original2433.index = 2433 := by decide

def c2433 : Contract := original2433.toContract.get (by decide)
theorem binding2433 : original2433.toContract = some c2433 := rfl

theorem checked2433 : check 4000 c2433 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2434 : RawOriginal := C019.records[2]'(by decide)
theorem original_id2434 : original2434.index = 2434 := by decide

def c2434 : Contract := original2434.toContract.get (by decide)
theorem binding2434 : original2434.toContract = some c2434 := rfl

theorem checked2434 : check 4000 c2434 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2435 : RawOriginal := C019.records[3]'(by decide)
theorem original_id2435 : original2435.index = 2435 := by decide

def c2435 : Contract := original2435.toContract.get (by decide)
theorem binding2435 : original2435.toContract = some c2435 := rfl

theorem checked2435 : check 4000 c2435 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2436 : RawOriginal := C019.records[4]'(by decide)
theorem original_id2436 : original2436.index = 2436 := by decide

def c2436 : Contract := original2436.toContract.get (by decide)
theorem binding2436 : original2436.toContract = some c2436 := rfl

theorem checked2436 : check 4000 c2436 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2437 : RawOriginal := C019.records[5]'(by decide)
theorem original_id2437 : original2437.index = 2437 := by decide

def c2437 : Contract := original2437.toContract.get (by decide)
theorem binding2437 : original2437.toContract = some c2437 := rfl

theorem checked2437 : check 4000 c2437 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2422, c2422, 4000, checked2422⟩,
  ⟨2423, c2423, 4000, checked2423⟩,
  ⟨2424, c2424, 4000, checked2424⟩,
  ⟨2425, c2425, 4000, checked2425⟩,
  ⟨2426, c2426, 4000, checked2426⟩,
  ⟨2427, c2427, 4000, checked2427⟩,
  ⟨2428, c2428, 4000, checked2428⟩,
  ⟨2429, c2429, 4000, checked2429⟩,
  ⟨2430, c2430, 4000, checked2430⟩,
  ⟨2431, c2431, 4000, checked2431⟩,
  ⟨2432, c2432, 4000, checked2432⟩,
  ⟨2433, c2433, 4000, checked2433⟩,
  ⟨2434, c2434, 4000, checked2434⟩,
  ⟨2435, c2435, 4000, checked2435⟩,
  ⟨2436, c2436, 4000, checked2436⟩,
  ⟨2437, c2437, 4000, checked2437⟩]

end PA215.ContractShards.Shard018Part7
