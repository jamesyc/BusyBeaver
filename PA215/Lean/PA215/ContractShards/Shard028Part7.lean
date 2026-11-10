import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C028
import PA215.Census.C029
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard028Part7
open PA215.Contracts PA215.Census

def original3702 : RawOriginal := C028.records[118]'(by decide)
theorem original_id3702 : original3702.index = 3702 := by decide

def c3702 : Contract := original3702.toContract.get (by decide)
theorem binding3702 : original3702.toContract = some c3702 := rfl

theorem checked3702 : check 4000 c3702 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3703 : RawOriginal := C028.records[119]'(by decide)
theorem original_id3703 : original3703.index = 3703 := by decide

def c3703 : Contract := original3703.toContract.get (by decide)
theorem binding3703 : original3703.toContract = some c3703 := rfl

theorem checked3703 : check 4000 c3703 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3704 : RawOriginal := C028.records[120]'(by decide)
theorem original_id3704 : original3704.index = 3704 := by decide

def c3704 : Contract := original3704.toContract.get (by decide)
theorem binding3704 : original3704.toContract = some c3704 := rfl

theorem checked3704 : check 4000 c3704 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3705 : RawOriginal := C028.records[121]'(by decide)
theorem original_id3705 : original3705.index = 3705 := by decide

def c3705 : Contract := original3705.toContract.get (by decide)
theorem binding3705 : original3705.toContract = some c3705 := rfl

theorem checked3705 : check 4000 c3705 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3706 : RawOriginal := C028.records[122]'(by decide)
theorem original_id3706 : original3706.index = 3706 := by decide

def c3706 : Contract := original3706.toContract.get (by decide)
theorem binding3706 : original3706.toContract = some c3706 := rfl

theorem checked3706 : check 4000 c3706 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3707 : RawOriginal := C028.records[123]'(by decide)
theorem original_id3707 : original3707.index = 3707 := by decide

def c3707 : Contract := original3707.toContract.get (by decide)
theorem binding3707 : original3707.toContract = some c3707 := rfl

theorem checked3707 : check 4000 c3707 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3708 : RawOriginal := C028.records[124]'(by decide)
theorem original_id3708 : original3708.index = 3708 := by decide

def c3708 : Contract := original3708.toContract.get (by decide)
theorem binding3708 : original3708.toContract = some c3708 := rfl

theorem checked3708 : check 4000 c3708 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3709 : RawOriginal := C028.records[125]'(by decide)
theorem original_id3709 : original3709.index = 3709 := by decide

def c3709 : Contract := original3709.toContract.get (by decide)
theorem binding3709 : original3709.toContract = some c3709 := rfl

theorem checked3709 : check 4000 c3709 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3710 : RawOriginal := C028.records[126]'(by decide)
theorem original_id3710 : original3710.index = 3710 := by decide

def c3710 : Contract := original3710.toContract.get (by decide)
theorem binding3710 : original3710.toContract = some c3710 := rfl

theorem checked3710 : check 4000 c3710 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3711 : RawOriginal := C028.records[127]'(by decide)
theorem original_id3711 : original3711.index = 3711 := by decide

def c3711 : Contract := original3711.toContract.get (by decide)
theorem binding3711 : original3711.toContract = some c3711 := rfl

theorem checked3711 : check 4000 c3711 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3712 : RawOriginal := C029.records[0]'(by decide)
theorem original_id3712 : original3712.index = 3712 := by decide

def c3712 : Contract := original3712.toContract.get (by decide)
theorem binding3712 : original3712.toContract = some c3712 := rfl

theorem checked3712 : check 4000 c3712 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3713 : RawOriginal := C029.records[1]'(by decide)
theorem original_id3713 : original3713.index = 3713 := by decide

def c3713 : Contract := original3713.toContract.get (by decide)
theorem binding3713 : original3713.toContract = some c3713 := rfl

theorem checked3713 : check 4000 c3713 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3714 : RawOriginal := C029.records[2]'(by decide)
theorem original_id3714 : original3714.index = 3714 := by decide

def c3714 : Contract := original3714.toContract.get (by decide)
theorem binding3714 : original3714.toContract = some c3714 := rfl

theorem checked3714 : check 4000 c3714 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3715 : RawOriginal := C029.records[3]'(by decide)
theorem original_id3715 : original3715.index = 3715 := by decide

def c3715 : Contract := original3715.toContract.get (by decide)
theorem binding3715 : original3715.toContract = some c3715 := rfl

theorem checked3715 : check 4000 c3715 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3716 : RawOriginal := C029.records[4]'(by decide)
theorem original_id3716 : original3716.index = 3716 := by decide

def c3716 : Contract := original3716.toContract.get (by decide)
theorem binding3716 : original3716.toContract = some c3716 := rfl

theorem checked3716 : check 4000 c3716 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3717 : RawOriginal := C029.records[5]'(by decide)
theorem original_id3717 : original3717.index = 3717 := by decide

def c3717 : Contract := original3717.toContract.get (by decide)
theorem binding3717 : original3717.toContract = some c3717 := rfl

theorem checked3717 : check 4000 c3717 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3702, c3702, 4000, checked3702⟩,
  ⟨3703, c3703, 4000, checked3703⟩,
  ⟨3704, c3704, 4000, checked3704⟩,
  ⟨3705, c3705, 4000, checked3705⟩,
  ⟨3706, c3706, 4000, checked3706⟩,
  ⟨3707, c3707, 4000, checked3707⟩,
  ⟨3708, c3708, 4000, checked3708⟩,
  ⟨3709, c3709, 4000, checked3709⟩,
  ⟨3710, c3710, 4000, checked3710⟩,
  ⟨3711, c3711, 4000, checked3711⟩,
  ⟨3712, c3712, 4000, checked3712⟩,
  ⟨3713, c3713, 4000, checked3713⟩,
  ⟨3714, c3714, 4000, checked3714⟩,
  ⟨3715, c3715, 4000, checked3715⟩,
  ⟨3716, c3716, 4000, checked3716⟩,
  ⟨3717, c3717, 4000, checked3717⟩]

end PA215.ContractShards.Shard028Part7
