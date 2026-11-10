import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C030
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard030Part1
open PA215.Contracts PA215.Census

def original3862 : RawOriginal := C030.records[22]'(by decide)
theorem original_id3862 : original3862.index = 3862 := by decide

def c3862 : Contract := original3862.toContract.get (by decide)
theorem binding3862 : original3862.toContract = some c3862 := rfl

theorem checked3862 : check 4000 c3862 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3863 : RawOriginal := C030.records[23]'(by decide)
theorem original_id3863 : original3863.index = 3863 := by decide

def c3863 : Contract := original3863.toContract.get (by decide)
theorem binding3863 : original3863.toContract = some c3863 := rfl

theorem checked3863 : check 4000 c3863 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3864 : RawOriginal := C030.records[24]'(by decide)
theorem original_id3864 : original3864.index = 3864 := by decide

def c3864 : Contract := original3864.toContract.get (by decide)
theorem binding3864 : original3864.toContract = some c3864 := rfl

theorem checked3864 : check 4000 c3864 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3865 : RawOriginal := C030.records[25]'(by decide)
theorem original_id3865 : original3865.index = 3865 := by decide

def c3865 : Contract := original3865.toContract.get (by decide)
theorem binding3865 : original3865.toContract = some c3865 := rfl

theorem checked3865 : check 4000 c3865 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3866 : RawOriginal := C030.records[26]'(by decide)
theorem original_id3866 : original3866.index = 3866 := by decide

def c3866 : Contract := original3866.toContract.get (by decide)
theorem binding3866 : original3866.toContract = some c3866 := rfl

theorem checked3866 : check 4000 c3866 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3867 : RawOriginal := C030.records[27]'(by decide)
theorem original_id3867 : original3867.index = 3867 := by decide

def c3867 : Contract := original3867.toContract.get (by decide)
theorem binding3867 : original3867.toContract = some c3867 := rfl

theorem checked3867 : check 4000 c3867 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3868 : RawOriginal := C030.records[28]'(by decide)
theorem original_id3868 : original3868.index = 3868 := by decide

def c3868 : Contract := original3868.toContract.get (by decide)
theorem binding3868 : original3868.toContract = some c3868 := rfl

theorem checked3868 : check 4000 c3868 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3869 : RawOriginal := C030.records[29]'(by decide)
theorem original_id3869 : original3869.index = 3869 := by decide

def c3869 : Contract := original3869.toContract.get (by decide)
theorem binding3869 : original3869.toContract = some c3869 := rfl

theorem checked3869 : check 4000 c3869 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3870 : RawOriginal := C030.records[30]'(by decide)
theorem original_id3870 : original3870.index = 3870 := by decide

def c3870 : Contract := original3870.toContract.get (by decide)
theorem binding3870 : original3870.toContract = some c3870 := rfl

theorem checked3870 : check 4000 c3870 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3871 : RawOriginal := C030.records[31]'(by decide)
theorem original_id3871 : original3871.index = 3871 := by decide

def c3871 : Contract := original3871.toContract.get (by decide)
theorem binding3871 : original3871.toContract = some c3871 := rfl

theorem checked3871 : check 4000 c3871 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3872 : RawOriginal := C030.records[32]'(by decide)
theorem original_id3872 : original3872.index = 3872 := by decide

def c3872 : Contract := original3872.toContract.get (by decide)
theorem binding3872 : original3872.toContract = some c3872 := rfl

theorem checked3872 : check 4000 c3872 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3873 : RawOriginal := C030.records[33]'(by decide)
theorem original_id3873 : original3873.index = 3873 := by decide

def c3873 : Contract := original3873.toContract.get (by decide)
theorem binding3873 : original3873.toContract = some c3873 := rfl

theorem checked3873 : check 4000 c3873 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3874 : RawOriginal := C030.records[34]'(by decide)
theorem original_id3874 : original3874.index = 3874 := by decide

def c3874 : Contract := original3874.toContract.get (by decide)
theorem binding3874 : original3874.toContract = some c3874 := rfl

theorem checked3874 : check 4000 c3874 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3875 : RawOriginal := C030.records[35]'(by decide)
theorem original_id3875 : original3875.index = 3875 := by decide

def c3875 : Contract := original3875.toContract.get (by decide)
theorem binding3875 : original3875.toContract = some c3875 := rfl

theorem checked3875 : check 4000 c3875 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3876 : RawOriginal := C030.records[36]'(by decide)
theorem original_id3876 : original3876.index = 3876 := by decide

def c3876 : Contract := original3876.toContract.get (by decide)
theorem binding3876 : original3876.toContract = some c3876 := rfl

theorem checked3876 : check 4000 c3876 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3877 : RawOriginal := C030.records[37]'(by decide)
theorem original_id3877 : original3877.index = 3877 := by decide

def c3877 : Contract := original3877.toContract.get (by decide)
theorem binding3877 : original3877.toContract = some c3877 := rfl

theorem checked3877 : check 4000 c3877 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3862, c3862, 4000, checked3862⟩,
  ⟨3863, c3863, 4000, checked3863⟩,
  ⟨3864, c3864, 4000, checked3864⟩,
  ⟨3865, c3865, 4000, checked3865⟩,
  ⟨3866, c3866, 4000, checked3866⟩,
  ⟨3867, c3867, 4000, checked3867⟩,
  ⟨3868, c3868, 4000, checked3868⟩,
  ⟨3869, c3869, 4000, checked3869⟩,
  ⟨3870, c3870, 4000, checked3870⟩,
  ⟨3871, c3871, 4000, checked3871⟩,
  ⟨3872, c3872, 4000, checked3872⟩,
  ⟨3873, c3873, 4000, checked3873⟩,
  ⟨3874, c3874, 4000, checked3874⟩,
  ⟨3875, c3875, 4000, checked3875⟩,
  ⟨3876, c3876, 4000, checked3876⟩,
  ⟨3877, c3877, 4000, checked3877⟩]

end PA215.ContractShards.Shard030Part1
