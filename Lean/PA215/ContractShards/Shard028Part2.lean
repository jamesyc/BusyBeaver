import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C028
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard028Part2
open PA215.Contracts PA215.Census

def original3622 : RawOriginal := C028.records[38]'(by decide)
theorem original_id3622 : original3622.index = 3622 := by decide

def c3622 : Contract := original3622.toContract.get (by decide)
theorem binding3622 : original3622.toContract = some c3622 := rfl

theorem checked3622 : check 4000 c3622 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3623 : RawOriginal := C028.records[39]'(by decide)
theorem original_id3623 : original3623.index = 3623 := by decide

def c3623 : Contract := original3623.toContract.get (by decide)
theorem binding3623 : original3623.toContract = some c3623 := rfl

theorem checked3623 : check 4000 c3623 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3624 : RawOriginal := C028.records[40]'(by decide)
theorem original_id3624 : original3624.index = 3624 := by decide

def c3624 : Contract := original3624.toContract.get (by decide)
theorem binding3624 : original3624.toContract = some c3624 := rfl

theorem checked3624 : check 4000 c3624 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3625 : RawOriginal := C028.records[41]'(by decide)
theorem original_id3625 : original3625.index = 3625 := by decide

def c3625 : Contract := original3625.toContract.get (by decide)
theorem binding3625 : original3625.toContract = some c3625 := rfl

theorem checked3625 : check 4000 c3625 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3626 : RawOriginal := C028.records[42]'(by decide)
theorem original_id3626 : original3626.index = 3626 := by decide

def c3626 : Contract := original3626.toContract.get (by decide)
theorem binding3626 : original3626.toContract = some c3626 := rfl

theorem checked3626 : check 4000 c3626 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3627 : RawOriginal := C028.records[43]'(by decide)
theorem original_id3627 : original3627.index = 3627 := by decide

def c3627 : Contract := original3627.toContract.get (by decide)
theorem binding3627 : original3627.toContract = some c3627 := rfl

theorem checked3627 : check 4000 c3627 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3628 : RawOriginal := C028.records[44]'(by decide)
theorem original_id3628 : original3628.index = 3628 := by decide

def c3628 : Contract := original3628.toContract.get (by decide)
theorem binding3628 : original3628.toContract = some c3628 := rfl

theorem checked3628 : check 4000 c3628 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3629 : RawOriginal := C028.records[45]'(by decide)
theorem original_id3629 : original3629.index = 3629 := by decide

def c3629 : Contract := original3629.toContract.get (by decide)
theorem binding3629 : original3629.toContract = some c3629 := rfl

theorem checked3629 : check 4000 c3629 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3630 : RawOriginal := C028.records[46]'(by decide)
theorem original_id3630 : original3630.index = 3630 := by decide

def c3630 : Contract := original3630.toContract.get (by decide)
theorem binding3630 : original3630.toContract = some c3630 := rfl

theorem checked3630 : check 4000 c3630 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3631 : RawOriginal := C028.records[47]'(by decide)
theorem original_id3631 : original3631.index = 3631 := by decide

def c3631 : Contract := original3631.toContract.get (by decide)
theorem binding3631 : original3631.toContract = some c3631 := rfl

theorem checked3631 : check 4000 c3631 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3632 : RawOriginal := C028.records[48]'(by decide)
theorem original_id3632 : original3632.index = 3632 := by decide

def c3632 : Contract := original3632.toContract.get (by decide)
theorem binding3632 : original3632.toContract = some c3632 := rfl

theorem checked3632 : check 4000 c3632 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3633 : RawOriginal := C028.records[49]'(by decide)
theorem original_id3633 : original3633.index = 3633 := by decide

def c3633 : Contract := original3633.toContract.get (by decide)
theorem binding3633 : original3633.toContract = some c3633 := rfl

theorem checked3633 : check 4000 c3633 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3634 : RawOriginal := C028.records[50]'(by decide)
theorem original_id3634 : original3634.index = 3634 := by decide

def c3634 : Contract := original3634.toContract.get (by decide)
theorem binding3634 : original3634.toContract = some c3634 := rfl

theorem checked3634 : check 4000 c3634 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3635 : RawOriginal := C028.records[51]'(by decide)
theorem original_id3635 : original3635.index = 3635 := by decide

def c3635 : Contract := original3635.toContract.get (by decide)
theorem binding3635 : original3635.toContract = some c3635 := rfl

theorem checked3635 : check 4000 c3635 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3636 : RawOriginal := C028.records[52]'(by decide)
theorem original_id3636 : original3636.index = 3636 := by decide

def c3636 : Contract := original3636.toContract.get (by decide)
theorem binding3636 : original3636.toContract = some c3636 := rfl

theorem checked3636 : check 4000 c3636 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3637 : RawOriginal := C028.records[53]'(by decide)
theorem original_id3637 : original3637.index = 3637 := by decide

def c3637 : Contract := original3637.toContract.get (by decide)
theorem binding3637 : original3637.toContract = some c3637 := rfl

theorem checked3637 : check 4000 c3637 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3622, c3622, 4000, checked3622⟩,
  ⟨3623, c3623, 4000, checked3623⟩,
  ⟨3624, c3624, 4000, checked3624⟩,
  ⟨3625, c3625, 4000, checked3625⟩,
  ⟨3626, c3626, 4000, checked3626⟩,
  ⟨3627, c3627, 4000, checked3627⟩,
  ⟨3628, c3628, 4000, checked3628⟩,
  ⟨3629, c3629, 4000, checked3629⟩,
  ⟨3630, c3630, 4000, checked3630⟩,
  ⟨3631, c3631, 4000, checked3631⟩,
  ⟨3632, c3632, 4000, checked3632⟩,
  ⟨3633, c3633, 4000, checked3633⟩,
  ⟨3634, c3634, 4000, checked3634⟩,
  ⟨3635, c3635, 4000, checked3635⟩,
  ⟨3636, c3636, 4000, checked3636⟩,
  ⟨3637, c3637, 4000, checked3637⟩]

end PA215.ContractShards.Shard028Part2
