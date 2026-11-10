import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C026
import PA215.Census.C027
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard026Part7
open PA215.Contracts PA215.Census

def original3446 : RawOriginal := C026.records[118]'(by decide)
theorem original_id3446 : original3446.index = 3446 := by decide

def c3446 : Contract := original3446.toContract.get (by decide)
theorem binding3446 : original3446.toContract = some c3446 := rfl

theorem checked3446 : check 4000 c3446 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3447 : RawOriginal := C026.records[119]'(by decide)
theorem original_id3447 : original3447.index = 3447 := by decide

def c3447 : Contract := original3447.toContract.get (by decide)
theorem binding3447 : original3447.toContract = some c3447 := rfl

theorem checked3447 : check 4000 c3447 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3448 : RawOriginal := C026.records[120]'(by decide)
theorem original_id3448 : original3448.index = 3448 := by decide

def c3448 : Contract := original3448.toContract.get (by decide)
theorem binding3448 : original3448.toContract = some c3448 := rfl

theorem checked3448 : check 4000 c3448 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3449 : RawOriginal := C026.records[121]'(by decide)
theorem original_id3449 : original3449.index = 3449 := by decide

def c3449 : Contract := original3449.toContract.get (by decide)
theorem binding3449 : original3449.toContract = some c3449 := rfl

theorem checked3449 : check 4000 c3449 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3450 : RawOriginal := C026.records[122]'(by decide)
theorem original_id3450 : original3450.index = 3450 := by decide

def c3450 : Contract := original3450.toContract.get (by decide)
theorem binding3450 : original3450.toContract = some c3450 := rfl

theorem checked3450 : check 4000 c3450 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3451 : RawOriginal := C026.records[123]'(by decide)
theorem original_id3451 : original3451.index = 3451 := by decide

def c3451 : Contract := original3451.toContract.get (by decide)
theorem binding3451 : original3451.toContract = some c3451 := rfl

theorem checked3451 : check 4000 c3451 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3452 : RawOriginal := C026.records[124]'(by decide)
theorem original_id3452 : original3452.index = 3452 := by decide

def c3452 : Contract := original3452.toContract.get (by decide)
theorem binding3452 : original3452.toContract = some c3452 := rfl

theorem checked3452 : check 4000 c3452 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3453 : RawOriginal := C026.records[125]'(by decide)
theorem original_id3453 : original3453.index = 3453 := by decide

def c3453 : Contract := original3453.toContract.get (by decide)
theorem binding3453 : original3453.toContract = some c3453 := rfl

theorem checked3453 : check 4000 c3453 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3454 : RawOriginal := C026.records[126]'(by decide)
theorem original_id3454 : original3454.index = 3454 := by decide

def c3454 : Contract := original3454.toContract.get (by decide)
theorem binding3454 : original3454.toContract = some c3454 := rfl

theorem checked3454 : check 4000 c3454 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3455 : RawOriginal := C026.records[127]'(by decide)
theorem original_id3455 : original3455.index = 3455 := by decide

def c3455 : Contract := original3455.toContract.get (by decide)
theorem binding3455 : original3455.toContract = some c3455 := rfl

theorem checked3455 : check 4000 c3455 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3456 : RawOriginal := C027.records[0]'(by decide)
theorem original_id3456 : original3456.index = 3456 := by decide

def c3456 : Contract := original3456.toContract.get (by decide)
theorem binding3456 : original3456.toContract = some c3456 := rfl

theorem checked3456 : check 4000 c3456 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3457 : RawOriginal := C027.records[1]'(by decide)
theorem original_id3457 : original3457.index = 3457 := by decide

def c3457 : Contract := original3457.toContract.get (by decide)
theorem binding3457 : original3457.toContract = some c3457 := rfl

theorem checked3457 : check 4000 c3457 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3458 : RawOriginal := C027.records[2]'(by decide)
theorem original_id3458 : original3458.index = 3458 := by decide

def c3458 : Contract := original3458.toContract.get (by decide)
theorem binding3458 : original3458.toContract = some c3458 := rfl

theorem checked3458 : check 4000 c3458 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3459 : RawOriginal := C027.records[3]'(by decide)
theorem original_id3459 : original3459.index = 3459 := by decide

def c3459 : Contract := original3459.toContract.get (by decide)
theorem binding3459 : original3459.toContract = some c3459 := rfl

theorem checked3459 : check 4000 c3459 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3460 : RawOriginal := C027.records[4]'(by decide)
theorem original_id3460 : original3460.index = 3460 := by decide

def c3460 : Contract := original3460.toContract.get (by decide)
theorem binding3460 : original3460.toContract = some c3460 := rfl

theorem checked3460 : check 4000 c3460 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3461 : RawOriginal := C027.records[5]'(by decide)
theorem original_id3461 : original3461.index = 3461 := by decide

def c3461 : Contract := original3461.toContract.get (by decide)
theorem binding3461 : original3461.toContract = some c3461 := rfl

theorem checked3461 : check 4000 c3461 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3446, c3446, 4000, checked3446⟩,
  ⟨3447, c3447, 4000, checked3447⟩,
  ⟨3448, c3448, 4000, checked3448⟩,
  ⟨3449, c3449, 4000, checked3449⟩,
  ⟨3450, c3450, 4000, checked3450⟩,
  ⟨3451, c3451, 4000, checked3451⟩,
  ⟨3452, c3452, 4000, checked3452⟩,
  ⟨3453, c3453, 4000, checked3453⟩,
  ⟨3454, c3454, 4000, checked3454⟩,
  ⟨3455, c3455, 4000, checked3455⟩,
  ⟨3456, c3456, 4000, checked3456⟩,
  ⟨3457, c3457, 4000, checked3457⟩,
  ⟨3458, c3458, 4000, checked3458⟩,
  ⟨3459, c3459, 4000, checked3459⟩,
  ⟨3460, c3460, 4000, checked3460⟩,
  ⟨3461, c3461, 4000, checked3461⟩]

end PA215.ContractShards.Shard026Part7
