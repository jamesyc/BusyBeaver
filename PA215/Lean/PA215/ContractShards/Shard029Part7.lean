import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C029
import PA215.Census.C030
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard029Part7
open PA215.Contracts PA215.Census

def original3830 : RawOriginal := C029.records[118]'(by decide)
theorem original_id3830 : original3830.index = 3830 := by decide

def c3830 : Contract := original3830.toContract.get (by decide)
theorem binding3830 : original3830.toContract = some c3830 := rfl

theorem checked3830 : check 4000 c3830 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3831 : RawOriginal := C029.records[119]'(by decide)
theorem original_id3831 : original3831.index = 3831 := by decide

def c3831 : Contract := original3831.toContract.get (by decide)
theorem binding3831 : original3831.toContract = some c3831 := rfl

theorem checked3831 : check 4000 c3831 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3832 : RawOriginal := C029.records[120]'(by decide)
theorem original_id3832 : original3832.index = 3832 := by decide

def c3832 : Contract := original3832.toContract.get (by decide)
theorem binding3832 : original3832.toContract = some c3832 := rfl

theorem checked3832 : check 4000 c3832 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3833 : RawOriginal := C029.records[121]'(by decide)
theorem original_id3833 : original3833.index = 3833 := by decide

def c3833 : Contract := original3833.toContract.get (by decide)
theorem binding3833 : original3833.toContract = some c3833 := rfl

theorem checked3833 : check 4000 c3833 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3834 : RawOriginal := C029.records[122]'(by decide)
theorem original_id3834 : original3834.index = 3834 := by decide

def c3834 : Contract := original3834.toContract.get (by decide)
theorem binding3834 : original3834.toContract = some c3834 := rfl

theorem checked3834 : check 4000 c3834 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3835 : RawOriginal := C029.records[123]'(by decide)
theorem original_id3835 : original3835.index = 3835 := by decide

def c3835 : Contract := original3835.toContract.get (by decide)
theorem binding3835 : original3835.toContract = some c3835 := rfl

theorem checked3835 : check 4000 c3835 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3836 : RawOriginal := C029.records[124]'(by decide)
theorem original_id3836 : original3836.index = 3836 := by decide

def c3836 : Contract := original3836.toContract.get (by decide)
theorem binding3836 : original3836.toContract = some c3836 := rfl

theorem checked3836 : check 4000 c3836 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3837 : RawOriginal := C029.records[125]'(by decide)
theorem original_id3837 : original3837.index = 3837 := by decide

def c3837 : Contract := original3837.toContract.get (by decide)
theorem binding3837 : original3837.toContract = some c3837 := rfl

theorem checked3837 : check 4000 c3837 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3838 : RawOriginal := C029.records[126]'(by decide)
theorem original_id3838 : original3838.index = 3838 := by decide

def c3838 : Contract := original3838.toContract.get (by decide)
theorem binding3838 : original3838.toContract = some c3838 := rfl

theorem checked3838 : check 4000 c3838 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3839 : RawOriginal := C029.records[127]'(by decide)
theorem original_id3839 : original3839.index = 3839 := by decide

def c3839 : Contract := original3839.toContract.get (by decide)
theorem binding3839 : original3839.toContract = some c3839 := rfl

theorem checked3839 : check 4000 c3839 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3840 : RawOriginal := C030.records[0]'(by decide)
theorem original_id3840 : original3840.index = 3840 := by decide

def c3840 : Contract := original3840.toContract.get (by decide)
theorem binding3840 : original3840.toContract = some c3840 := rfl

theorem checked3840 : check 4000 c3840 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3841 : RawOriginal := C030.records[1]'(by decide)
theorem original_id3841 : original3841.index = 3841 := by decide

def c3841 : Contract := original3841.toContract.get (by decide)
theorem binding3841 : original3841.toContract = some c3841 := rfl

theorem checked3841 : check 4000 c3841 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3842 : RawOriginal := C030.records[2]'(by decide)
theorem original_id3842 : original3842.index = 3842 := by decide

def c3842 : Contract := original3842.toContract.get (by decide)
theorem binding3842 : original3842.toContract = some c3842 := rfl

theorem checked3842 : check 4000 c3842 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3843 : RawOriginal := C030.records[3]'(by decide)
theorem original_id3843 : original3843.index = 3843 := by decide

def c3843 : Contract := original3843.toContract.get (by decide)
theorem binding3843 : original3843.toContract = some c3843 := rfl

theorem checked3843 : check 4000 c3843 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3844 : RawOriginal := C030.records[4]'(by decide)
theorem original_id3844 : original3844.index = 3844 := by decide

def c3844 : Contract := original3844.toContract.get (by decide)
theorem binding3844 : original3844.toContract = some c3844 := rfl

theorem checked3844 : check 4000 c3844 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3845 : RawOriginal := C030.records[5]'(by decide)
theorem original_id3845 : original3845.index = 3845 := by decide

def c3845 : Contract := original3845.toContract.get (by decide)
theorem binding3845 : original3845.toContract = some c3845 := rfl

theorem checked3845 : check 4000 c3845 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3830, c3830, 4000, checked3830⟩,
  ⟨3831, c3831, 4000, checked3831⟩,
  ⟨3832, c3832, 4000, checked3832⟩,
  ⟨3833, c3833, 4000, checked3833⟩,
  ⟨3834, c3834, 4000, checked3834⟩,
  ⟨3835, c3835, 4000, checked3835⟩,
  ⟨3836, c3836, 4000, checked3836⟩,
  ⟨3837, c3837, 4000, checked3837⟩,
  ⟨3838, c3838, 4000, checked3838⟩,
  ⟨3839, c3839, 4000, checked3839⟩,
  ⟨3840, c3840, 4000, checked3840⟩,
  ⟨3841, c3841, 4000, checked3841⟩,
  ⟨3842, c3842, 4000, checked3842⟩,
  ⟨3843, c3843, 4000, checked3843⟩,
  ⟨3844, c3844, 4000, checked3844⟩,
  ⟨3845, c3845, 4000, checked3845⟩]

end PA215.ContractShards.Shard029Part7
