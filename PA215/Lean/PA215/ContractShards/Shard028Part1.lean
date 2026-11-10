import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C028
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard028Part1
open PA215.Contracts PA215.Census

def original3606 : RawOriginal := C028.records[22]'(by decide)
theorem original_id3606 : original3606.index = 3606 := by decide

def c3606 : Contract := original3606.toContract.get (by decide)
theorem binding3606 : original3606.toContract = some c3606 := rfl

theorem checked3606 : check 4000 c3606 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3607 : RawOriginal := C028.records[23]'(by decide)
theorem original_id3607 : original3607.index = 3607 := by decide

def c3607 : Contract := original3607.toContract.get (by decide)
theorem binding3607 : original3607.toContract = some c3607 := rfl

theorem checked3607 : check 4000 c3607 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3608 : RawOriginal := C028.records[24]'(by decide)
theorem original_id3608 : original3608.index = 3608 := by decide

def c3608 : Contract := original3608.toContract.get (by decide)
theorem binding3608 : original3608.toContract = some c3608 := rfl

theorem checked3608 : check 4000 c3608 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3609 : RawOriginal := C028.records[25]'(by decide)
theorem original_id3609 : original3609.index = 3609 := by decide

def c3609 : Contract := original3609.toContract.get (by decide)
theorem binding3609 : original3609.toContract = some c3609 := rfl

theorem checked3609 : check 4000 c3609 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3610 : RawOriginal := C028.records[26]'(by decide)
theorem original_id3610 : original3610.index = 3610 := by decide

def c3610 : Contract := original3610.toContract.get (by decide)
theorem binding3610 : original3610.toContract = some c3610 := rfl

theorem checked3610 : check 4000 c3610 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3611 : RawOriginal := C028.records[27]'(by decide)
theorem original_id3611 : original3611.index = 3611 := by decide

def c3611 : Contract := original3611.toContract.get (by decide)
theorem binding3611 : original3611.toContract = some c3611 := rfl

theorem checked3611 : check 4000 c3611 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3612 : RawOriginal := C028.records[28]'(by decide)
theorem original_id3612 : original3612.index = 3612 := by decide

def c3612 : Contract := original3612.toContract.get (by decide)
theorem binding3612 : original3612.toContract = some c3612 := rfl

theorem checked3612 : check 4000 c3612 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3613 : RawOriginal := C028.records[29]'(by decide)
theorem original_id3613 : original3613.index = 3613 := by decide

def c3613 : Contract := original3613.toContract.get (by decide)
theorem binding3613 : original3613.toContract = some c3613 := rfl

theorem checked3613 : check 4000 c3613 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3614 : RawOriginal := C028.records[30]'(by decide)
theorem original_id3614 : original3614.index = 3614 := by decide

def c3614 : Contract := original3614.toContract.get (by decide)
theorem binding3614 : original3614.toContract = some c3614 := rfl

theorem checked3614 : check 4000 c3614 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3615 : RawOriginal := C028.records[31]'(by decide)
theorem original_id3615 : original3615.index = 3615 := by decide

def c3615 : Contract := original3615.toContract.get (by decide)
theorem binding3615 : original3615.toContract = some c3615 := rfl

theorem checked3615 : check 4000 c3615 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3616 : RawOriginal := C028.records[32]'(by decide)
theorem original_id3616 : original3616.index = 3616 := by decide

def c3616 : Contract := original3616.toContract.get (by decide)
theorem binding3616 : original3616.toContract = some c3616 := rfl

theorem checked3616 : check 4000 c3616 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3617 : RawOriginal := C028.records[33]'(by decide)
theorem original_id3617 : original3617.index = 3617 := by decide

def c3617 : Contract := original3617.toContract.get (by decide)
theorem binding3617 : original3617.toContract = some c3617 := rfl

theorem checked3617 : check 4000 c3617 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3618 : RawOriginal := C028.records[34]'(by decide)
theorem original_id3618 : original3618.index = 3618 := by decide

def c3618 : Contract := original3618.toContract.get (by decide)
theorem binding3618 : original3618.toContract = some c3618 := rfl

theorem checked3618 : check 4000 c3618 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3619 : RawOriginal := C028.records[35]'(by decide)
theorem original_id3619 : original3619.index = 3619 := by decide

def c3619 : Contract := original3619.toContract.get (by decide)
theorem binding3619 : original3619.toContract = some c3619 := rfl

theorem checked3619 : check 4000 c3619 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3620 : RawOriginal := C028.records[36]'(by decide)
theorem original_id3620 : original3620.index = 3620 := by decide

def c3620 : Contract := original3620.toContract.get (by decide)
theorem binding3620 : original3620.toContract = some c3620 := rfl

theorem checked3620 : check 4000 c3620 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3621 : RawOriginal := C028.records[37]'(by decide)
theorem original_id3621 : original3621.index = 3621 := by decide

def c3621 : Contract := original3621.toContract.get (by decide)
theorem binding3621 : original3621.toContract = some c3621 := rfl

theorem checked3621 : check 4000 c3621 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3606, c3606, 4000, checked3606⟩,
  ⟨3607, c3607, 4000, checked3607⟩,
  ⟨3608, c3608, 4000, checked3608⟩,
  ⟨3609, c3609, 4000, checked3609⟩,
  ⟨3610, c3610, 4000, checked3610⟩,
  ⟨3611, c3611, 4000, checked3611⟩,
  ⟨3612, c3612, 4000, checked3612⟩,
  ⟨3613, c3613, 4000, checked3613⟩,
  ⟨3614, c3614, 4000, checked3614⟩,
  ⟨3615, c3615, 4000, checked3615⟩,
  ⟨3616, c3616, 4000, checked3616⟩,
  ⟨3617, c3617, 4000, checked3617⟩,
  ⟨3618, c3618, 4000, checked3618⟩,
  ⟨3619, c3619, 4000, checked3619⟩,
  ⟨3620, c3620, 4000, checked3620⟩,
  ⟨3621, c3621, 4000, checked3621⟩]

end PA215.ContractShards.Shard028Part1
