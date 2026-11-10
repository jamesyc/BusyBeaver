import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C030
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard030Part4
open PA215.Contracts PA215.Census

def original3910 : RawOriginal := C030.records[70]'(by decide)
theorem original_id3910 : original3910.index = 3910 := by decide

def c3910 : Contract := original3910.toContract.get (by decide)
theorem binding3910 : original3910.toContract = some c3910 := rfl

theorem checked3910 : check 4000 c3910 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3911 : RawOriginal := C030.records[71]'(by decide)
theorem original_id3911 : original3911.index = 3911 := by decide

def c3911 : Contract := original3911.toContract.get (by decide)
theorem binding3911 : original3911.toContract = some c3911 := rfl

theorem checked3911 : check 4000 c3911 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3912 : RawOriginal := C030.records[72]'(by decide)
theorem original_id3912 : original3912.index = 3912 := by decide

def c3912 : Contract := original3912.toContract.get (by decide)
theorem binding3912 : original3912.toContract = some c3912 := rfl

theorem checked3912 : check 4000 c3912 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3913 : RawOriginal := C030.records[73]'(by decide)
theorem original_id3913 : original3913.index = 3913 := by decide

def c3913 : Contract := original3913.toContract.get (by decide)
theorem binding3913 : original3913.toContract = some c3913 := rfl

theorem checked3913 : check 4000 c3913 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3914 : RawOriginal := C030.records[74]'(by decide)
theorem original_id3914 : original3914.index = 3914 := by decide

def c3914 : Contract := original3914.toContract.get (by decide)
theorem binding3914 : original3914.toContract = some c3914 := rfl

theorem checked3914 : check 4000 c3914 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3915 : RawOriginal := C030.records[75]'(by decide)
theorem original_id3915 : original3915.index = 3915 := by decide

def c3915 : Contract := original3915.toContract.get (by decide)
theorem binding3915 : original3915.toContract = some c3915 := rfl

theorem checked3915 : check 4000 c3915 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3916 : RawOriginal := C030.records[76]'(by decide)
theorem original_id3916 : original3916.index = 3916 := by decide

def c3916 : Contract := original3916.toContract.get (by decide)
theorem binding3916 : original3916.toContract = some c3916 := rfl

theorem checked3916 : check 4000 c3916 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3917 : RawOriginal := C030.records[77]'(by decide)
theorem original_id3917 : original3917.index = 3917 := by decide

def c3917 : Contract := original3917.toContract.get (by decide)
theorem binding3917 : original3917.toContract = some c3917 := rfl

theorem checked3917 : check 4000 c3917 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3918 : RawOriginal := C030.records[78]'(by decide)
theorem original_id3918 : original3918.index = 3918 := by decide

def c3918 : Contract := original3918.toContract.get (by decide)
theorem binding3918 : original3918.toContract = some c3918 := rfl

theorem checked3918 : check 4000 c3918 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3919 : RawOriginal := C030.records[79]'(by decide)
theorem original_id3919 : original3919.index = 3919 := by decide

def c3919 : Contract := original3919.toContract.get (by decide)
theorem binding3919 : original3919.toContract = some c3919 := rfl

theorem checked3919 : check 4000 c3919 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3920 : RawOriginal := C030.records[80]'(by decide)
theorem original_id3920 : original3920.index = 3920 := by decide

def c3920 : Contract := original3920.toContract.get (by decide)
theorem binding3920 : original3920.toContract = some c3920 := rfl

theorem checked3920 : check 4000 c3920 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3921 : RawOriginal := C030.records[81]'(by decide)
theorem original_id3921 : original3921.index = 3921 := by decide

def c3921 : Contract := original3921.toContract.get (by decide)
theorem binding3921 : original3921.toContract = some c3921 := rfl

theorem checked3921 : check 4000 c3921 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3922 : RawOriginal := C030.records[82]'(by decide)
theorem original_id3922 : original3922.index = 3922 := by decide

def c3922 : Contract := original3922.toContract.get (by decide)
theorem binding3922 : original3922.toContract = some c3922 := rfl

theorem checked3922 : check 4000 c3922 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3923 : RawOriginal := C030.records[83]'(by decide)
theorem original_id3923 : original3923.index = 3923 := by decide

def c3923 : Contract := original3923.toContract.get (by decide)
theorem binding3923 : original3923.toContract = some c3923 := rfl

theorem checked3923 : check 4000 c3923 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3924 : RawOriginal := C030.records[84]'(by decide)
theorem original_id3924 : original3924.index = 3924 := by decide

def c3924 : Contract := original3924.toContract.get (by decide)
theorem binding3924 : original3924.toContract = some c3924 := rfl

theorem checked3924 : check 4000 c3924 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3925 : RawOriginal := C030.records[85]'(by decide)
theorem original_id3925 : original3925.index = 3925 := by decide

def c3925 : Contract := original3925.toContract.get (by decide)
theorem binding3925 : original3925.toContract = some c3925 := rfl

theorem checked3925 : check 4000 c3925 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3910, c3910, 4000, checked3910⟩,
  ⟨3911, c3911, 4000, checked3911⟩,
  ⟨3912, c3912, 4000, checked3912⟩,
  ⟨3913, c3913, 4000, checked3913⟩,
  ⟨3914, c3914, 4000, checked3914⟩,
  ⟨3915, c3915, 4000, checked3915⟩,
  ⟨3916, c3916, 4000, checked3916⟩,
  ⟨3917, c3917, 4000, checked3917⟩,
  ⟨3918, c3918, 4000, checked3918⟩,
  ⟨3919, c3919, 4000, checked3919⟩,
  ⟨3920, c3920, 4000, checked3920⟩,
  ⟨3921, c3921, 4000, checked3921⟩,
  ⟨3922, c3922, 4000, checked3922⟩,
  ⟨3923, c3923, 4000, checked3923⟩,
  ⟨3924, c3924, 4000, checked3924⟩,
  ⟨3925, c3925, 4000, checked3925⟩]

end PA215.ContractShards.Shard030Part4
