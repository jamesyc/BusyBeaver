import PA215.CertifiedContracts
import PA215.Census.C008
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard008Part1
open PA215.Contracts PA215.Census

def original1046 : RawOriginal := C008.records[22]'(by decide)
theorem original_id1046 : original1046.index = 1046 := by decide

def c1046 : Contract := original1046.toContract.get (by decide)
theorem binding1046 : original1046.toContract = some c1046 := rfl

theorem checked1046 : check 4000 c1046 = true := by decide

def original1047 : RawOriginal := C008.records[23]'(by decide)
theorem original_id1047 : original1047.index = 1047 := by decide

def c1047 : Contract := original1047.toContract.get (by decide)
theorem binding1047 : original1047.toContract = some c1047 := rfl

theorem checked1047 : check 4000 c1047 = true := by decide

def original1048 : RawOriginal := C008.records[24]'(by decide)
theorem original_id1048 : original1048.index = 1048 := by decide

def c1048 : Contract := original1048.toContract.get (by decide)
theorem binding1048 : original1048.toContract = some c1048 := rfl

theorem checked1048 : check 4000 c1048 = true := by decide

def original1049 : RawOriginal := C008.records[25]'(by decide)
theorem original_id1049 : original1049.index = 1049 := by decide

def c1049 : Contract := original1049.toContract.get (by decide)
theorem binding1049 : original1049.toContract = some c1049 := rfl

theorem checked1049 : check 4000 c1049 = true := by decide

def original1050 : RawOriginal := C008.records[26]'(by decide)
theorem original_id1050 : original1050.index = 1050 := by decide

def c1050 : Contract := original1050.toContract.get (by decide)
theorem binding1050 : original1050.toContract = some c1050 := rfl

theorem checked1050 : check 4000 c1050 = true := by decide

def original1051 : RawOriginal := C008.records[27]'(by decide)
theorem original_id1051 : original1051.index = 1051 := by decide

def c1051 : Contract := original1051.toContract.get (by decide)
theorem binding1051 : original1051.toContract = some c1051 := rfl

theorem checked1051 : check 4000 c1051 = true := by decide

def original1052 : RawOriginal := C008.records[28]'(by decide)
theorem original_id1052 : original1052.index = 1052 := by decide

def c1052 : Contract := original1052.toContract.get (by decide)
theorem binding1052 : original1052.toContract = some c1052 := rfl

theorem checked1052 : check 4000 c1052 = true := by decide

def original1053 : RawOriginal := C008.records[29]'(by decide)
theorem original_id1053 : original1053.index = 1053 := by decide

def c1053 : Contract := original1053.toContract.get (by decide)
theorem binding1053 : original1053.toContract = some c1053 := rfl

theorem checked1053 : check 4000 c1053 = true := by decide

def original1054 : RawOriginal := C008.records[30]'(by decide)
theorem original_id1054 : original1054.index = 1054 := by decide

def c1054 : Contract := original1054.toContract.get (by decide)
theorem binding1054 : original1054.toContract = some c1054 := rfl

theorem checked1054 : check 4000 c1054 = true := by decide

def original1055 : RawOriginal := C008.records[31]'(by decide)
theorem original_id1055 : original1055.index = 1055 := by decide

def c1055 : Contract := original1055.toContract.get (by decide)
theorem binding1055 : original1055.toContract = some c1055 := rfl

theorem checked1055 : check 4000 c1055 = true := by decide

def original1056 : RawOriginal := C008.records[32]'(by decide)
theorem original_id1056 : original1056.index = 1056 := by decide

def c1056 : Contract := original1056.toContract.get (by decide)
theorem binding1056 : original1056.toContract = some c1056 := rfl

theorem checked1056 : check 4000 c1056 = true := by decide

def original1057 : RawOriginal := C008.records[33]'(by decide)
theorem original_id1057 : original1057.index = 1057 := by decide

def c1057 : Contract := original1057.toContract.get (by decide)
theorem binding1057 : original1057.toContract = some c1057 := rfl

theorem checked1057 : check 4000 c1057 = true := by decide

def original1058 : RawOriginal := C008.records[34]'(by decide)
theorem original_id1058 : original1058.index = 1058 := by decide

def c1058 : Contract := original1058.toContract.get (by decide)
theorem binding1058 : original1058.toContract = some c1058 := rfl

theorem checked1058 : check 4000 c1058 = true := by decide

def original1059 : RawOriginal := C008.records[35]'(by decide)
theorem original_id1059 : original1059.index = 1059 := by decide

def c1059 : Contract := original1059.toContract.get (by decide)
theorem binding1059 : original1059.toContract = some c1059 := rfl

theorem checked1059 : check 4000 c1059 = true := by decide

def original1060 : RawOriginal := C008.records[36]'(by decide)
theorem original_id1060 : original1060.index = 1060 := by decide

def c1060 : Contract := original1060.toContract.get (by decide)
theorem binding1060 : original1060.toContract = some c1060 := rfl

theorem checked1060 : check 4000 c1060 = true := by decide

def original1061 : RawOriginal := C008.records[37]'(by decide)
theorem original_id1061 : original1061.index = 1061 := by decide

def c1061 : Contract := original1061.toContract.get (by decide)
theorem binding1061 : original1061.toContract = some c1061 := rfl

theorem checked1061 : check 4000 c1061 = true := by decide

def records : List Certified := [
  ⟨1046, c1046, 4000, checked1046⟩,
  ⟨1047, c1047, 4000, checked1047⟩,
  ⟨1048, c1048, 4000, checked1048⟩,
  ⟨1049, c1049, 4000, checked1049⟩,
  ⟨1050, c1050, 4000, checked1050⟩,
  ⟨1051, c1051, 4000, checked1051⟩,
  ⟨1052, c1052, 4000, checked1052⟩,
  ⟨1053, c1053, 4000, checked1053⟩,
  ⟨1054, c1054, 4000, checked1054⟩,
  ⟨1055, c1055, 4000, checked1055⟩,
  ⟨1056, c1056, 4000, checked1056⟩,
  ⟨1057, c1057, 4000, checked1057⟩,
  ⟨1058, c1058, 4000, checked1058⟩,
  ⟨1059, c1059, 4000, checked1059⟩,
  ⟨1060, c1060, 4000, checked1060⟩,
  ⟨1061, c1061, 4000, checked1061⟩]

end PA215.ContractShards.Shard008Part1
