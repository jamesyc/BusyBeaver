import PA215.CertifiedContracts
import PA215.Census.C008
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard008Part3
open PA215.Contracts PA215.Census

def original1078 : RawOriginal := C008.records[54]'(by decide)
theorem original_id1078 : original1078.index = 1078 := by decide

def c1078 : Contract := original1078.toContract.get (by decide)
theorem binding1078 : original1078.toContract = some c1078 := rfl

theorem checked1078 : check 4000 c1078 = true := by decide

def original1079 : RawOriginal := C008.records[55]'(by decide)
theorem original_id1079 : original1079.index = 1079 := by decide

def c1079 : Contract := original1079.toContract.get (by decide)
theorem binding1079 : original1079.toContract = some c1079 := rfl

theorem checked1079 : check 4000 c1079 = true := by decide

def original1080 : RawOriginal := C008.records[56]'(by decide)
theorem original_id1080 : original1080.index = 1080 := by decide

def c1080 : Contract := original1080.toContract.get (by decide)
theorem binding1080 : original1080.toContract = some c1080 := rfl

theorem checked1080 : check 4000 c1080 = true := by decide

def original1081 : RawOriginal := C008.records[57]'(by decide)
theorem original_id1081 : original1081.index = 1081 := by decide

def c1081 : Contract := original1081.toContract.get (by decide)
theorem binding1081 : original1081.toContract = some c1081 := rfl

theorem checked1081 : check 4000 c1081 = true := by decide

def original1082 : RawOriginal := C008.records[58]'(by decide)
theorem original_id1082 : original1082.index = 1082 := by decide

def c1082 : Contract := original1082.toContract.get (by decide)
theorem binding1082 : original1082.toContract = some c1082 := rfl

theorem checked1082 : check 4000 c1082 = true := by decide

def original1083 : RawOriginal := C008.records[59]'(by decide)
theorem original_id1083 : original1083.index = 1083 := by decide

def c1083 : Contract := original1083.toContract.get (by decide)
theorem binding1083 : original1083.toContract = some c1083 := rfl

theorem checked1083 : check 4000 c1083 = true := by decide

def original1084 : RawOriginal := C008.records[60]'(by decide)
theorem original_id1084 : original1084.index = 1084 := by decide

def c1084 : Contract := original1084.toContract.get (by decide)
theorem binding1084 : original1084.toContract = some c1084 := rfl

theorem checked1084 : check 4000 c1084 = true := by decide

def original1085 : RawOriginal := C008.records[61]'(by decide)
theorem original_id1085 : original1085.index = 1085 := by decide

def c1085 : Contract := original1085.toContract.get (by decide)
theorem binding1085 : original1085.toContract = some c1085 := rfl

theorem checked1085 : check 4000 c1085 = true := by decide

def original1086 : RawOriginal := C008.records[62]'(by decide)
theorem original_id1086 : original1086.index = 1086 := by decide

def c1086 : Contract := original1086.toContract.get (by decide)
theorem binding1086 : original1086.toContract = some c1086 := rfl

theorem checked1086 : check 4000 c1086 = true := by decide

def original1087 : RawOriginal := C008.records[63]'(by decide)
theorem original_id1087 : original1087.index = 1087 := by decide

def c1087 : Contract := original1087.toContract.get (by decide)
theorem binding1087 : original1087.toContract = some c1087 := rfl

theorem checked1087 : check 4000 c1087 = true := by decide

def original1088 : RawOriginal := C008.records[64]'(by decide)
theorem original_id1088 : original1088.index = 1088 := by decide

def c1088 : Contract := original1088.toContract.get (by decide)
theorem binding1088 : original1088.toContract = some c1088 := rfl

theorem checked1088 : check 4000 c1088 = true := by decide

def original1089 : RawOriginal := C008.records[65]'(by decide)
theorem original_id1089 : original1089.index = 1089 := by decide

def c1089 : Contract := original1089.toContract.get (by decide)
theorem binding1089 : original1089.toContract = some c1089 := rfl

theorem checked1089 : check 4000 c1089 = true := by decide

def original1090 : RawOriginal := C008.records[66]'(by decide)
theorem original_id1090 : original1090.index = 1090 := by decide

def c1090 : Contract := original1090.toContract.get (by decide)
theorem binding1090 : original1090.toContract = some c1090 := rfl

theorem checked1090 : check 4000 c1090 = true := by decide

def original1091 : RawOriginal := C008.records[67]'(by decide)
theorem original_id1091 : original1091.index = 1091 := by decide

def c1091 : Contract := original1091.toContract.get (by decide)
theorem binding1091 : original1091.toContract = some c1091 := rfl

theorem checked1091 : check 4000 c1091 = true := by decide

def original1092 : RawOriginal := C008.records[68]'(by decide)
theorem original_id1092 : original1092.index = 1092 := by decide

def c1092 : Contract := original1092.toContract.get (by decide)
theorem binding1092 : original1092.toContract = some c1092 := rfl

theorem checked1092 : check 4000 c1092 = true := by decide

def original1093 : RawOriginal := C008.records[69]'(by decide)
theorem original_id1093 : original1093.index = 1093 := by decide

def c1093 : Contract := original1093.toContract.get (by decide)
theorem binding1093 : original1093.toContract = some c1093 := rfl

theorem checked1093 : check 4000 c1093 = true := by decide

def records : List Certified := [
  ⟨1078, c1078, 4000, checked1078⟩,
  ⟨1079, c1079, 4000, checked1079⟩,
  ⟨1080, c1080, 4000, checked1080⟩,
  ⟨1081, c1081, 4000, checked1081⟩,
  ⟨1082, c1082, 4000, checked1082⟩,
  ⟨1083, c1083, 4000, checked1083⟩,
  ⟨1084, c1084, 4000, checked1084⟩,
  ⟨1085, c1085, 4000, checked1085⟩,
  ⟨1086, c1086, 4000, checked1086⟩,
  ⟨1087, c1087, 4000, checked1087⟩,
  ⟨1088, c1088, 4000, checked1088⟩,
  ⟨1089, c1089, 4000, checked1089⟩,
  ⟨1090, c1090, 4000, checked1090⟩,
  ⟨1091, c1091, 4000, checked1091⟩,
  ⟨1092, c1092, 4000, checked1092⟩,
  ⟨1093, c1093, 4000, checked1093⟩]

end PA215.ContractShards.Shard008Part3
