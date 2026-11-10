import PA215.CertifiedContracts
import PA215.Census.C008
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard008Part0
open PA215.Contracts PA215.Census

def original1030 : RawOriginal := C008.records[6]'(by decide)
theorem original_id1030 : original1030.index = 1030 := by decide

def c1030 : Contract := original1030.toContract.get (by decide)
theorem binding1030 : original1030.toContract = some c1030 := rfl

theorem checked1030 : check 4000 c1030 = true := by decide

def original1031 : RawOriginal := C008.records[7]'(by decide)
theorem original_id1031 : original1031.index = 1031 := by decide

def c1031 : Contract := original1031.toContract.get (by decide)
theorem binding1031 : original1031.toContract = some c1031 := rfl

theorem checked1031 : check 4000 c1031 = true := by decide

def original1032 : RawOriginal := C008.records[8]'(by decide)
theorem original_id1032 : original1032.index = 1032 := by decide

def c1032 : Contract := original1032.toContract.get (by decide)
theorem binding1032 : original1032.toContract = some c1032 := rfl

theorem checked1032 : check 4000 c1032 = true := by decide

def original1033 : RawOriginal := C008.records[9]'(by decide)
theorem original_id1033 : original1033.index = 1033 := by decide

def c1033 : Contract := original1033.toContract.get (by decide)
theorem binding1033 : original1033.toContract = some c1033 := rfl

theorem checked1033 : check 4000 c1033 = true := by decide

def original1034 : RawOriginal := C008.records[10]'(by decide)
theorem original_id1034 : original1034.index = 1034 := by decide

def c1034 : Contract := original1034.toContract.get (by decide)
theorem binding1034 : original1034.toContract = some c1034 := rfl

theorem checked1034 : check 4000 c1034 = true := by decide

def original1035 : RawOriginal := C008.records[11]'(by decide)
theorem original_id1035 : original1035.index = 1035 := by decide

def c1035 : Contract := original1035.toContract.get (by decide)
theorem binding1035 : original1035.toContract = some c1035 := rfl

theorem checked1035 : check 4000 c1035 = true := by decide

def original1036 : RawOriginal := C008.records[12]'(by decide)
theorem original_id1036 : original1036.index = 1036 := by decide

def c1036 : Contract := original1036.toContract.get (by decide)
theorem binding1036 : original1036.toContract = some c1036 := rfl

theorem checked1036 : check 4000 c1036 = true := by decide

def original1037 : RawOriginal := C008.records[13]'(by decide)
theorem original_id1037 : original1037.index = 1037 := by decide

def c1037 : Contract := original1037.toContract.get (by decide)
theorem binding1037 : original1037.toContract = some c1037 := rfl

theorem checked1037 : check 4000 c1037 = true := by decide

def original1038 : RawOriginal := C008.records[14]'(by decide)
theorem original_id1038 : original1038.index = 1038 := by decide

def c1038 : Contract := original1038.toContract.get (by decide)
theorem binding1038 : original1038.toContract = some c1038 := rfl

theorem checked1038 : check 4000 c1038 = true := by decide

def original1039 : RawOriginal := C008.records[15]'(by decide)
theorem original_id1039 : original1039.index = 1039 := by decide

def c1039 : Contract := original1039.toContract.get (by decide)
theorem binding1039 : original1039.toContract = some c1039 := rfl

theorem checked1039 : check 4000 c1039 = true := by decide

def original1040 : RawOriginal := C008.records[16]'(by decide)
theorem original_id1040 : original1040.index = 1040 := by decide

def c1040 : Contract := original1040.toContract.get (by decide)
theorem binding1040 : original1040.toContract = some c1040 := rfl

theorem checked1040 : check 4000 c1040 = true := by decide

def original1041 : RawOriginal := C008.records[17]'(by decide)
theorem original_id1041 : original1041.index = 1041 := by decide

def c1041 : Contract := original1041.toContract.get (by decide)
theorem binding1041 : original1041.toContract = some c1041 := rfl

theorem checked1041 : check 4000 c1041 = true := by decide

def original1042 : RawOriginal := C008.records[18]'(by decide)
theorem original_id1042 : original1042.index = 1042 := by decide

def c1042 : Contract := original1042.toContract.get (by decide)
theorem binding1042 : original1042.toContract = some c1042 := rfl

theorem checked1042 : check 4000 c1042 = true := by decide

def original1043 : RawOriginal := C008.records[19]'(by decide)
theorem original_id1043 : original1043.index = 1043 := by decide

def c1043 : Contract := original1043.toContract.get (by decide)
theorem binding1043 : original1043.toContract = some c1043 := rfl

theorem checked1043 : check 4000 c1043 = true := by decide

def original1044 : RawOriginal := C008.records[20]'(by decide)
theorem original_id1044 : original1044.index = 1044 := by decide

def c1044 : Contract := original1044.toContract.get (by decide)
theorem binding1044 : original1044.toContract = some c1044 := rfl

theorem checked1044 : check 4000 c1044 = true := by decide

def original1045 : RawOriginal := C008.records[21]'(by decide)
theorem original_id1045 : original1045.index = 1045 := by decide

def c1045 : Contract := original1045.toContract.get (by decide)
theorem binding1045 : original1045.toContract = some c1045 := rfl

theorem checked1045 : check 4000 c1045 = true := by decide

def records : List Certified := [
  ⟨1030, c1030, 4000, checked1030⟩,
  ⟨1031, c1031, 4000, checked1031⟩,
  ⟨1032, c1032, 4000, checked1032⟩,
  ⟨1033, c1033, 4000, checked1033⟩,
  ⟨1034, c1034, 4000, checked1034⟩,
  ⟨1035, c1035, 4000, checked1035⟩,
  ⟨1036, c1036, 4000, checked1036⟩,
  ⟨1037, c1037, 4000, checked1037⟩,
  ⟨1038, c1038, 4000, checked1038⟩,
  ⟨1039, c1039, 4000, checked1039⟩,
  ⟨1040, c1040, 4000, checked1040⟩,
  ⟨1041, c1041, 4000, checked1041⟩,
  ⟨1042, c1042, 4000, checked1042⟩,
  ⟨1043, c1043, 4000, checked1043⟩,
  ⟨1044, c1044, 4000, checked1044⟩,
  ⟨1045, c1045, 4000, checked1045⟩]

end PA215.ContractShards.Shard008Part0
