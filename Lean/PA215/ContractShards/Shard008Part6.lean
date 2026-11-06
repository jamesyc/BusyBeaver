import PA215.CertifiedContracts
import PA215.Census.C008
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard008Part6
open PA215.Contracts PA215.Census

def original1126 : RawOriginal := C008.records[102]'(by decide)
theorem original_id1126 : original1126.index = 1126 := by decide

def c1126 : Contract := original1126.toContract.get (by decide)
theorem binding1126 : original1126.toContract = some c1126 := rfl

theorem checked1126 : check 4000 c1126 = true := by decide

def original1127 : RawOriginal := C008.records[103]'(by decide)
theorem original_id1127 : original1127.index = 1127 := by decide

def c1127 : Contract := original1127.toContract.get (by decide)
theorem binding1127 : original1127.toContract = some c1127 := rfl

theorem checked1127 : check 4000 c1127 = true := by decide

def original1128 : RawOriginal := C008.records[104]'(by decide)
theorem original_id1128 : original1128.index = 1128 := by decide

def c1128 : Contract := original1128.toContract.get (by decide)
theorem binding1128 : original1128.toContract = some c1128 := rfl

theorem checked1128 : check 4000 c1128 = true := by decide

def original1129 : RawOriginal := C008.records[105]'(by decide)
theorem original_id1129 : original1129.index = 1129 := by decide

def c1129 : Contract := original1129.toContract.get (by decide)
theorem binding1129 : original1129.toContract = some c1129 := rfl

theorem checked1129 : check 4000 c1129 = true := by decide

def original1130 : RawOriginal := C008.records[106]'(by decide)
theorem original_id1130 : original1130.index = 1130 := by decide

def c1130 : Contract := original1130.toContract.get (by decide)
theorem binding1130 : original1130.toContract = some c1130 := rfl

theorem checked1130 : check 4000 c1130 = true := by decide

def original1131 : RawOriginal := C008.records[107]'(by decide)
theorem original_id1131 : original1131.index = 1131 := by decide

def c1131 : Contract := original1131.toContract.get (by decide)
theorem binding1131 : original1131.toContract = some c1131 := rfl

theorem checked1131 : check 4000 c1131 = true := by decide

def original1132 : RawOriginal := C008.records[108]'(by decide)
theorem original_id1132 : original1132.index = 1132 := by decide

def c1132 : Contract := original1132.toContract.get (by decide)
theorem binding1132 : original1132.toContract = some c1132 := rfl

theorem checked1132 : check 4000 c1132 = true := by decide

def original1133 : RawOriginal := C008.records[109]'(by decide)
theorem original_id1133 : original1133.index = 1133 := by decide

def c1133 : Contract := original1133.toContract.get (by decide)
theorem binding1133 : original1133.toContract = some c1133 := rfl

theorem checked1133 : check 4000 c1133 = true := by decide

def original1134 : RawOriginal := C008.records[110]'(by decide)
theorem original_id1134 : original1134.index = 1134 := by decide

def c1134 : Contract := original1134.toContract.get (by decide)
theorem binding1134 : original1134.toContract = some c1134 := rfl

theorem checked1134 : check 4000 c1134 = true := by decide

def original1135 : RawOriginal := C008.records[111]'(by decide)
theorem original_id1135 : original1135.index = 1135 := by decide

def c1135 : Contract := original1135.toContract.get (by decide)
theorem binding1135 : original1135.toContract = some c1135 := rfl

theorem checked1135 : check 4000 c1135 = true := by decide

def original1136 : RawOriginal := C008.records[112]'(by decide)
theorem original_id1136 : original1136.index = 1136 := by decide

def c1136 : Contract := original1136.toContract.get (by decide)
theorem binding1136 : original1136.toContract = some c1136 := rfl

theorem checked1136 : check 4000 c1136 = true := by decide

def original1137 : RawOriginal := C008.records[113]'(by decide)
theorem original_id1137 : original1137.index = 1137 := by decide

def c1137 : Contract := original1137.toContract.get (by decide)
theorem binding1137 : original1137.toContract = some c1137 := rfl

theorem checked1137 : check 4000 c1137 = true := by decide

def original1138 : RawOriginal := C008.records[114]'(by decide)
theorem original_id1138 : original1138.index = 1138 := by decide

def c1138 : Contract := original1138.toContract.get (by decide)
theorem binding1138 : original1138.toContract = some c1138 := rfl

theorem checked1138 : check 4000 c1138 = true := by decide

def original1139 : RawOriginal := C008.records[115]'(by decide)
theorem original_id1139 : original1139.index = 1139 := by decide

def c1139 : Contract := original1139.toContract.get (by decide)
theorem binding1139 : original1139.toContract = some c1139 := rfl

theorem checked1139 : check 4000 c1139 = true := by decide

def original1140 : RawOriginal := C008.records[116]'(by decide)
theorem original_id1140 : original1140.index = 1140 := by decide

def c1140 : Contract := original1140.toContract.get (by decide)
theorem binding1140 : original1140.toContract = some c1140 := rfl

theorem checked1140 : check 4000 c1140 = true := by decide

def original1141 : RawOriginal := C008.records[117]'(by decide)
theorem original_id1141 : original1141.index = 1141 := by decide

def c1141 : Contract := original1141.toContract.get (by decide)
theorem binding1141 : original1141.toContract = some c1141 := rfl

theorem checked1141 : check 4000 c1141 = true := by decide

def records : List Certified := [
  ⟨1126, c1126, 4000, checked1126⟩,
  ⟨1127, c1127, 4000, checked1127⟩,
  ⟨1128, c1128, 4000, checked1128⟩,
  ⟨1129, c1129, 4000, checked1129⟩,
  ⟨1130, c1130, 4000, checked1130⟩,
  ⟨1131, c1131, 4000, checked1131⟩,
  ⟨1132, c1132, 4000, checked1132⟩,
  ⟨1133, c1133, 4000, checked1133⟩,
  ⟨1134, c1134, 4000, checked1134⟩,
  ⟨1135, c1135, 4000, checked1135⟩,
  ⟨1136, c1136, 4000, checked1136⟩,
  ⟨1137, c1137, 4000, checked1137⟩,
  ⟨1138, c1138, 4000, checked1138⟩,
  ⟨1139, c1139, 4000, checked1139⟩,
  ⟨1140, c1140, 4000, checked1140⟩,
  ⟨1141, c1141, 4000, checked1141⟩]

end PA215.ContractShards.Shard008Part6
