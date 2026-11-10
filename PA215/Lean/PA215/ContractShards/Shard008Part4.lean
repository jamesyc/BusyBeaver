import PA215.CertifiedContracts
import PA215.Census.C008
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard008Part4
open PA215.Contracts PA215.Census

def original1094 : RawOriginal := C008.records[70]'(by decide)
theorem original_id1094 : original1094.index = 1094 := by decide

def c1094 : Contract := original1094.toContract.get (by decide)
theorem binding1094 : original1094.toContract = some c1094 := rfl

theorem checked1094 : check 4000 c1094 = true := by decide

def original1095 : RawOriginal := C008.records[71]'(by decide)
theorem original_id1095 : original1095.index = 1095 := by decide

def c1095 : Contract := original1095.toContract.get (by decide)
theorem binding1095 : original1095.toContract = some c1095 := rfl

theorem checked1095 : check 4000 c1095 = true := by decide

def original1096 : RawOriginal := C008.records[72]'(by decide)
theorem original_id1096 : original1096.index = 1096 := by decide

def c1096 : Contract := original1096.toContract.get (by decide)
theorem binding1096 : original1096.toContract = some c1096 := rfl

theorem checked1096 : check 4000 c1096 = true := by decide

def original1097 : RawOriginal := C008.records[73]'(by decide)
theorem original_id1097 : original1097.index = 1097 := by decide

def c1097 : Contract := original1097.toContract.get (by decide)
theorem binding1097 : original1097.toContract = some c1097 := rfl

theorem checked1097 : check 4000 c1097 = true := by decide

def original1098 : RawOriginal := C008.records[74]'(by decide)
theorem original_id1098 : original1098.index = 1098 := by decide

def c1098 : Contract := original1098.toContract.get (by decide)
theorem binding1098 : original1098.toContract = some c1098 := rfl

theorem checked1098 : check 4000 c1098 = true := by decide

def original1099 : RawOriginal := C008.records[75]'(by decide)
theorem original_id1099 : original1099.index = 1099 := by decide

def c1099 : Contract := original1099.toContract.get (by decide)
theorem binding1099 : original1099.toContract = some c1099 := rfl

theorem checked1099 : check 4000 c1099 = true := by decide

def original1100 : RawOriginal := C008.records[76]'(by decide)
theorem original_id1100 : original1100.index = 1100 := by decide

def c1100 : Contract := original1100.toContract.get (by decide)
theorem binding1100 : original1100.toContract = some c1100 := rfl

theorem checked1100 : check 4000 c1100 = true := by decide

def original1101 : RawOriginal := C008.records[77]'(by decide)
theorem original_id1101 : original1101.index = 1101 := by decide

def c1101 : Contract := original1101.toContract.get (by decide)
theorem binding1101 : original1101.toContract = some c1101 := rfl

theorem checked1101 : check 4000 c1101 = true := by decide

def original1102 : RawOriginal := C008.records[78]'(by decide)
theorem original_id1102 : original1102.index = 1102 := by decide

def c1102 : Contract := original1102.toContract.get (by decide)
theorem binding1102 : original1102.toContract = some c1102 := rfl

theorem checked1102 : check 4000 c1102 = true := by decide

def original1103 : RawOriginal := C008.records[79]'(by decide)
theorem original_id1103 : original1103.index = 1103 := by decide

def c1103 : Contract := original1103.toContract.get (by decide)
theorem binding1103 : original1103.toContract = some c1103 := rfl

theorem checked1103 : check 4000 c1103 = true := by decide

def original1104 : RawOriginal := C008.records[80]'(by decide)
theorem original_id1104 : original1104.index = 1104 := by decide

def c1104 : Contract := original1104.toContract.get (by decide)
theorem binding1104 : original1104.toContract = some c1104 := rfl

theorem checked1104 : check 4000 c1104 = true := by decide

def original1105 : RawOriginal := C008.records[81]'(by decide)
theorem original_id1105 : original1105.index = 1105 := by decide

def c1105 : Contract := original1105.toContract.get (by decide)
theorem binding1105 : original1105.toContract = some c1105 := rfl

theorem checked1105 : check 4000 c1105 = true := by decide

def original1106 : RawOriginal := C008.records[82]'(by decide)
theorem original_id1106 : original1106.index = 1106 := by decide

def c1106 : Contract := original1106.toContract.get (by decide)
theorem binding1106 : original1106.toContract = some c1106 := rfl

theorem checked1106 : check 4000 c1106 = true := by decide

def original1107 : RawOriginal := C008.records[83]'(by decide)
theorem original_id1107 : original1107.index = 1107 := by decide

def c1107 : Contract := original1107.toContract.get (by decide)
theorem binding1107 : original1107.toContract = some c1107 := rfl

theorem checked1107 : check 4000 c1107 = true := by decide

def original1108 : RawOriginal := C008.records[84]'(by decide)
theorem original_id1108 : original1108.index = 1108 := by decide

def c1108 : Contract := original1108.toContract.get (by decide)
theorem binding1108 : original1108.toContract = some c1108 := rfl

theorem checked1108 : check 4000 c1108 = true := by decide

def original1109 : RawOriginal := C008.records[85]'(by decide)
theorem original_id1109 : original1109.index = 1109 := by decide

def c1109 : Contract := original1109.toContract.get (by decide)
theorem binding1109 : original1109.toContract = some c1109 := rfl

theorem checked1109 : check 4000 c1109 = true := by decide

def records : List Certified := [
  ⟨1094, c1094, 4000, checked1094⟩,
  ⟨1095, c1095, 4000, checked1095⟩,
  ⟨1096, c1096, 4000, checked1096⟩,
  ⟨1097, c1097, 4000, checked1097⟩,
  ⟨1098, c1098, 4000, checked1098⟩,
  ⟨1099, c1099, 4000, checked1099⟩,
  ⟨1100, c1100, 4000, checked1100⟩,
  ⟨1101, c1101, 4000, checked1101⟩,
  ⟨1102, c1102, 4000, checked1102⟩,
  ⟨1103, c1103, 4000, checked1103⟩,
  ⟨1104, c1104, 4000, checked1104⟩,
  ⟨1105, c1105, 4000, checked1105⟩,
  ⟨1106, c1106, 4000, checked1106⟩,
  ⟨1107, c1107, 4000, checked1107⟩,
  ⟨1108, c1108, 4000, checked1108⟩,
  ⟨1109, c1109, 4000, checked1109⟩]

end PA215.ContractShards.Shard008Part4
