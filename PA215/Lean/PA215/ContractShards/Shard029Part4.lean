import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C029
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard029Part4
open PA215.Contracts PA215.Census

def original3782 : RawOriginal := C029.records[70]'(by decide)
theorem original_id3782 : original3782.index = 3782 := by decide

def c3782 : Contract := original3782.toContract.get (by decide)
theorem binding3782 : original3782.toContract = some c3782 := rfl

theorem checked3782 : check 4000 c3782 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3783 : RawOriginal := C029.records[71]'(by decide)
theorem original_id3783 : original3783.index = 3783 := by decide

def c3783 : Contract := original3783.toContract.get (by decide)
theorem binding3783 : original3783.toContract = some c3783 := rfl

theorem checked3783 : check 4000 c3783 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3784 : RawOriginal := C029.records[72]'(by decide)
theorem original_id3784 : original3784.index = 3784 := by decide

def c3784 : Contract := original3784.toContract.get (by decide)
theorem binding3784 : original3784.toContract = some c3784 := rfl

theorem checked3784 : check 4000 c3784 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3785 : RawOriginal := C029.records[73]'(by decide)
theorem original_id3785 : original3785.index = 3785 := by decide

def c3785 : Contract := original3785.toContract.get (by decide)
theorem binding3785 : original3785.toContract = some c3785 := rfl

theorem checked3785 : check 4000 c3785 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3786 : RawOriginal := C029.records[74]'(by decide)
theorem original_id3786 : original3786.index = 3786 := by decide

def c3786 : Contract := original3786.toContract.get (by decide)
theorem binding3786 : original3786.toContract = some c3786 := rfl

theorem checked3786 : check 4000 c3786 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3787 : RawOriginal := C029.records[75]'(by decide)
theorem original_id3787 : original3787.index = 3787 := by decide

def c3787 : Contract := original3787.toContract.get (by decide)
theorem binding3787 : original3787.toContract = some c3787 := rfl

theorem checked3787 : check 4000 c3787 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3788 : RawOriginal := C029.records[76]'(by decide)
theorem original_id3788 : original3788.index = 3788 := by decide

def c3788 : Contract := original3788.toContract.get (by decide)
theorem binding3788 : original3788.toContract = some c3788 := rfl

theorem checked3788 : check 4000 c3788 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3789 : RawOriginal := C029.records[77]'(by decide)
theorem original_id3789 : original3789.index = 3789 := by decide

def c3789 : Contract := original3789.toContract.get (by decide)
theorem binding3789 : original3789.toContract = some c3789 := rfl

theorem checked3789 : check 4000 c3789 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3790 : RawOriginal := C029.records[78]'(by decide)
theorem original_id3790 : original3790.index = 3790 := by decide

def c3790 : Contract := original3790.toContract.get (by decide)
theorem binding3790 : original3790.toContract = some c3790 := rfl

theorem checked3790 : check 4000 c3790 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3791 : RawOriginal := C029.records[79]'(by decide)
theorem original_id3791 : original3791.index = 3791 := by decide

def c3791 : Contract := original3791.toContract.get (by decide)
theorem binding3791 : original3791.toContract = some c3791 := rfl

theorem checked3791 : check 4000 c3791 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3792 : RawOriginal := C029.records[80]'(by decide)
theorem original_id3792 : original3792.index = 3792 := by decide

def c3792 : Contract := original3792.toContract.get (by decide)
theorem binding3792 : original3792.toContract = some c3792 := rfl

theorem checked3792 : check 4000 c3792 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3793 : RawOriginal := C029.records[81]'(by decide)
theorem original_id3793 : original3793.index = 3793 := by decide

def c3793 : Contract := original3793.toContract.get (by decide)
theorem binding3793 : original3793.toContract = some c3793 := rfl

theorem checked3793 : check 4000 c3793 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3794 : RawOriginal := C029.records[82]'(by decide)
theorem original_id3794 : original3794.index = 3794 := by decide

def c3794 : Contract := original3794.toContract.get (by decide)
theorem binding3794 : original3794.toContract = some c3794 := rfl

theorem checked3794 : check 4000 c3794 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3795 : RawOriginal := C029.records[83]'(by decide)
theorem original_id3795 : original3795.index = 3795 := by decide

def c3795 : Contract := original3795.toContract.get (by decide)
theorem binding3795 : original3795.toContract = some c3795 := rfl

theorem checked3795 : check 4000 c3795 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3796 : RawOriginal := C029.records[84]'(by decide)
theorem original_id3796 : original3796.index = 3796 := by decide

def c3796 : Contract := original3796.toContract.get (by decide)
theorem binding3796 : original3796.toContract = some c3796 := rfl

theorem checked3796 : check 4000 c3796 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3797 : RawOriginal := C029.records[85]'(by decide)
theorem original_id3797 : original3797.index = 3797 := by decide

def c3797 : Contract := original3797.toContract.get (by decide)
theorem binding3797 : original3797.toContract = some c3797 := rfl

theorem checked3797 : check 4000 c3797 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3782, c3782, 4000, checked3782⟩,
  ⟨3783, c3783, 4000, checked3783⟩,
  ⟨3784, c3784, 4000, checked3784⟩,
  ⟨3785, c3785, 4000, checked3785⟩,
  ⟨3786, c3786, 4000, checked3786⟩,
  ⟨3787, c3787, 4000, checked3787⟩,
  ⟨3788, c3788, 4000, checked3788⟩,
  ⟨3789, c3789, 4000, checked3789⟩,
  ⟨3790, c3790, 4000, checked3790⟩,
  ⟨3791, c3791, 4000, checked3791⟩,
  ⟨3792, c3792, 4000, checked3792⟩,
  ⟨3793, c3793, 4000, checked3793⟩,
  ⟨3794, c3794, 4000, checked3794⟩,
  ⟨3795, c3795, 4000, checked3795⟩,
  ⟨3796, c3796, 4000, checked3796⟩,
  ⟨3797, c3797, 4000, checked3797⟩]

end PA215.ContractShards.Shard029Part4
