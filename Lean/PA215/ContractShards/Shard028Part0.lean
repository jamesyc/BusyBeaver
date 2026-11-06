import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C028
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard028Part0
open PA215.Contracts PA215.Census

def original3590 : RawOriginal := C028.records[6]'(by decide)
theorem original_id3590 : original3590.index = 3590 := by decide

def c3590 : Contract := original3590.toContract.get (by decide)
theorem binding3590 : original3590.toContract = some c3590 := rfl

theorem checked3590 : check 4000 c3590 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3591 : RawOriginal := C028.records[7]'(by decide)
theorem original_id3591 : original3591.index = 3591 := by decide

def c3591 : Contract := original3591.toContract.get (by decide)
theorem binding3591 : original3591.toContract = some c3591 := rfl

theorem checked3591 : check 4000 c3591 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3592 : RawOriginal := C028.records[8]'(by decide)
theorem original_id3592 : original3592.index = 3592 := by decide

def c3592 : Contract := original3592.toContract.get (by decide)
theorem binding3592 : original3592.toContract = some c3592 := rfl

theorem checked3592 : check 4000 c3592 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3593 : RawOriginal := C028.records[9]'(by decide)
theorem original_id3593 : original3593.index = 3593 := by decide

def c3593 : Contract := original3593.toContract.get (by decide)
theorem binding3593 : original3593.toContract = some c3593 := rfl

theorem checked3593 : check 4000 c3593 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3594 : RawOriginal := C028.records[10]'(by decide)
theorem original_id3594 : original3594.index = 3594 := by decide

def c3594 : Contract := original3594.toContract.get (by decide)
theorem binding3594 : original3594.toContract = some c3594 := rfl

theorem checked3594 : check 4000 c3594 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3595 : RawOriginal := C028.records[11]'(by decide)
theorem original_id3595 : original3595.index = 3595 := by decide

def c3595 : Contract := original3595.toContract.get (by decide)
theorem binding3595 : original3595.toContract = some c3595 := rfl

theorem checked3595 : check 4000 c3595 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3596 : RawOriginal := C028.records[12]'(by decide)
theorem original_id3596 : original3596.index = 3596 := by decide

def c3596 : Contract := original3596.toContract.get (by decide)
theorem binding3596 : original3596.toContract = some c3596 := rfl

theorem checked3596 : check 4000 c3596 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3597 : RawOriginal := C028.records[13]'(by decide)
theorem original_id3597 : original3597.index = 3597 := by decide

def c3597 : Contract := original3597.toContract.get (by decide)
theorem binding3597 : original3597.toContract = some c3597 := rfl

theorem checked3597 : check 4000 c3597 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3598 : RawOriginal := C028.records[14]'(by decide)
theorem original_id3598 : original3598.index = 3598 := by decide

def c3598 : Contract := original3598.toContract.get (by decide)
theorem binding3598 : original3598.toContract = some c3598 := rfl

theorem checked3598 : check 4000 c3598 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3599 : RawOriginal := C028.records[15]'(by decide)
theorem original_id3599 : original3599.index = 3599 := by decide

def c3599 : Contract := original3599.toContract.get (by decide)
theorem binding3599 : original3599.toContract = some c3599 := rfl

theorem checked3599 : check 4000 c3599 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3600 : RawOriginal := C028.records[16]'(by decide)
theorem original_id3600 : original3600.index = 3600 := by decide

def c3600 : Contract := original3600.toContract.get (by decide)
theorem binding3600 : original3600.toContract = some c3600 := rfl

theorem checked3600 : check 4000 c3600 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3601 : RawOriginal := C028.records[17]'(by decide)
theorem original_id3601 : original3601.index = 3601 := by decide

def c3601 : Contract := original3601.toContract.get (by decide)
theorem binding3601 : original3601.toContract = some c3601 := rfl

theorem checked3601 : check 4000 c3601 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3602 : RawOriginal := C028.records[18]'(by decide)
theorem original_id3602 : original3602.index = 3602 := by decide

def c3602 : Contract := original3602.toContract.get (by decide)
theorem binding3602 : original3602.toContract = some c3602 := rfl

theorem checked3602 : check 4000 c3602 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3603 : RawOriginal := C028.records[19]'(by decide)
theorem original_id3603 : original3603.index = 3603 := by decide

def c3603 : Contract := original3603.toContract.get (by decide)
theorem binding3603 : original3603.toContract = some c3603 := rfl

theorem checked3603 : check 4000 c3603 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3604 : RawOriginal := C028.records[20]'(by decide)
theorem original_id3604 : original3604.index = 3604 := by decide

def c3604 : Contract := original3604.toContract.get (by decide)
theorem binding3604 : original3604.toContract = some c3604 := rfl

theorem checked3604 : check 4000 c3604 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3605 : RawOriginal := C028.records[21]'(by decide)
theorem original_id3605 : original3605.index = 3605 := by decide

def c3605 : Contract := original3605.toContract.get (by decide)
theorem binding3605 : original3605.toContract = some c3605 := rfl

theorem checked3605 : check 4000 c3605 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3590, c3590, 4000, checked3590⟩,
  ⟨3591, c3591, 4000, checked3591⟩,
  ⟨3592, c3592, 4000, checked3592⟩,
  ⟨3593, c3593, 4000, checked3593⟩,
  ⟨3594, c3594, 4000, checked3594⟩,
  ⟨3595, c3595, 4000, checked3595⟩,
  ⟨3596, c3596, 4000, checked3596⟩,
  ⟨3597, c3597, 4000, checked3597⟩,
  ⟨3598, c3598, 4000, checked3598⟩,
  ⟨3599, c3599, 4000, checked3599⟩,
  ⟨3600, c3600, 4000, checked3600⟩,
  ⟨3601, c3601, 4000, checked3601⟩,
  ⟨3602, c3602, 4000, checked3602⟩,
  ⟨3603, c3603, 4000, checked3603⟩,
  ⟨3604, c3604, 4000, checked3604⟩,
  ⟨3605, c3605, 4000, checked3605⟩]

end PA215.ContractShards.Shard028Part0
