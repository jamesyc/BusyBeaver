import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C029
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard029Part2
open PA215.Contracts PA215.Census

def original3750 : RawOriginal := C029.records[38]'(by decide)
theorem original_id3750 : original3750.index = 3750 := by decide

def c3750 : Contract := original3750.toContract.get (by decide)
theorem binding3750 : original3750.toContract = some c3750 := rfl

theorem checked3750 : check 4000 c3750 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3751 : RawOriginal := C029.records[39]'(by decide)
theorem original_id3751 : original3751.index = 3751 := by decide

def c3751 : Contract := original3751.toContract.get (by decide)
theorem binding3751 : original3751.toContract = some c3751 := rfl

theorem checked3751 : check 4000 c3751 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3752 : RawOriginal := C029.records[40]'(by decide)
theorem original_id3752 : original3752.index = 3752 := by decide

def c3752 : Contract := original3752.toContract.get (by decide)
theorem binding3752 : original3752.toContract = some c3752 := rfl

theorem checked3752 : check 4000 c3752 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3753 : RawOriginal := C029.records[41]'(by decide)
theorem original_id3753 : original3753.index = 3753 := by decide

def c3753 : Contract := original3753.toContract.get (by decide)
theorem binding3753 : original3753.toContract = some c3753 := rfl

theorem checked3753 : check 4000 c3753 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3754 : RawOriginal := C029.records[42]'(by decide)
theorem original_id3754 : original3754.index = 3754 := by decide

def c3754 : Contract := original3754.toContract.get (by decide)
theorem binding3754 : original3754.toContract = some c3754 := rfl

theorem checked3754 : check 4000 c3754 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3755 : RawOriginal := C029.records[43]'(by decide)
theorem original_id3755 : original3755.index = 3755 := by decide

def c3755 : Contract := original3755.toContract.get (by decide)
theorem binding3755 : original3755.toContract = some c3755 := rfl

theorem checked3755 : check 4000 c3755 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3756 : RawOriginal := C029.records[44]'(by decide)
theorem original_id3756 : original3756.index = 3756 := by decide

def c3756 : Contract := original3756.toContract.get (by decide)
theorem binding3756 : original3756.toContract = some c3756 := rfl

theorem checked3756 : check 4000 c3756 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3757 : RawOriginal := C029.records[45]'(by decide)
theorem original_id3757 : original3757.index = 3757 := by decide

def c3757 : Contract := original3757.toContract.get (by decide)
theorem binding3757 : original3757.toContract = some c3757 := rfl

theorem checked3757 : check 4000 c3757 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3758 : RawOriginal := C029.records[46]'(by decide)
theorem original_id3758 : original3758.index = 3758 := by decide

def c3758 : Contract := original3758.toContract.get (by decide)
theorem binding3758 : original3758.toContract = some c3758 := rfl

theorem checked3758 : check 4000 c3758 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3759 : RawOriginal := C029.records[47]'(by decide)
theorem original_id3759 : original3759.index = 3759 := by decide

def c3759 : Contract := original3759.toContract.get (by decide)
theorem binding3759 : original3759.toContract = some c3759 := rfl

theorem checked3759 : check 4000 c3759 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3760 : RawOriginal := C029.records[48]'(by decide)
theorem original_id3760 : original3760.index = 3760 := by decide

def c3760 : Contract := original3760.toContract.get (by decide)
theorem binding3760 : original3760.toContract = some c3760 := rfl

theorem checked3760 : check 4000 c3760 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3761 : RawOriginal := C029.records[49]'(by decide)
theorem original_id3761 : original3761.index = 3761 := by decide

def c3761 : Contract := original3761.toContract.get (by decide)
theorem binding3761 : original3761.toContract = some c3761 := rfl

theorem checked3761 : check 4000 c3761 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3762 : RawOriginal := C029.records[50]'(by decide)
theorem original_id3762 : original3762.index = 3762 := by decide

def c3762 : Contract := original3762.toContract.get (by decide)
theorem binding3762 : original3762.toContract = some c3762 := rfl

theorem checked3762 : check 4000 c3762 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3763 : RawOriginal := C029.records[51]'(by decide)
theorem original_id3763 : original3763.index = 3763 := by decide

def c3763 : Contract := original3763.toContract.get (by decide)
theorem binding3763 : original3763.toContract = some c3763 := rfl

theorem checked3763 : check 4000 c3763 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3764 : RawOriginal := C029.records[52]'(by decide)
theorem original_id3764 : original3764.index = 3764 := by decide

def c3764 : Contract := original3764.toContract.get (by decide)
theorem binding3764 : original3764.toContract = some c3764 := rfl

theorem checked3764 : check 4000 c3764 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3765 : RawOriginal := C029.records[53]'(by decide)
theorem original_id3765 : original3765.index = 3765 := by decide

def c3765 : Contract := original3765.toContract.get (by decide)
theorem binding3765 : original3765.toContract = some c3765 := rfl

theorem checked3765 : check 4000 c3765 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3750, c3750, 4000, checked3750⟩,
  ⟨3751, c3751, 4000, checked3751⟩,
  ⟨3752, c3752, 4000, checked3752⟩,
  ⟨3753, c3753, 4000, checked3753⟩,
  ⟨3754, c3754, 4000, checked3754⟩,
  ⟨3755, c3755, 4000, checked3755⟩,
  ⟨3756, c3756, 4000, checked3756⟩,
  ⟨3757, c3757, 4000, checked3757⟩,
  ⟨3758, c3758, 4000, checked3758⟩,
  ⟨3759, c3759, 4000, checked3759⟩,
  ⟨3760, c3760, 4000, checked3760⟩,
  ⟨3761, c3761, 4000, checked3761⟩,
  ⟨3762, c3762, 4000, checked3762⟩,
  ⟨3763, c3763, 4000, checked3763⟩,
  ⟨3764, c3764, 4000, checked3764⟩,
  ⟨3765, c3765, 4000, checked3765⟩]

end PA215.ContractShards.Shard029Part2
