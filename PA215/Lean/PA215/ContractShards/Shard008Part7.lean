import PA215.CertifiedContracts
import PA215.Census.C008
import PA215.Census.C009
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard008Part7
open PA215.Contracts PA215.Census

def original1142 : RawOriginal := C008.records[118]'(by decide)
theorem original_id1142 : original1142.index = 1142 := by decide

def c1142 : Contract := original1142.toContract.get (by decide)
theorem binding1142 : original1142.toContract = some c1142 := rfl

theorem checked1142 : check 4000 c1142 = true := by decide

def original1143 : RawOriginal := C008.records[119]'(by decide)
theorem original_id1143 : original1143.index = 1143 := by decide

def c1143 : Contract := original1143.toContract.get (by decide)
theorem binding1143 : original1143.toContract = some c1143 := rfl

theorem checked1143 : check 4000 c1143 = true := by decide

def original1144 : RawOriginal := C008.records[120]'(by decide)
theorem original_id1144 : original1144.index = 1144 := by decide

def c1144 : Contract := original1144.toContract.get (by decide)
theorem binding1144 : original1144.toContract = some c1144 := rfl

theorem checked1144 : check 4000 c1144 = true := by decide

def original1145 : RawOriginal := C008.records[121]'(by decide)
theorem original_id1145 : original1145.index = 1145 := by decide

def c1145 : Contract := original1145.toContract.get (by decide)
theorem binding1145 : original1145.toContract = some c1145 := rfl

theorem checked1145 : check 4000 c1145 = true := by decide

def original1146 : RawOriginal := C008.records[122]'(by decide)
theorem original_id1146 : original1146.index = 1146 := by decide

def c1146 : Contract := original1146.toContract.get (by decide)
theorem binding1146 : original1146.toContract = some c1146 := rfl

theorem checked1146 : check 4000 c1146 = true := by decide

def original1147 : RawOriginal := C008.records[123]'(by decide)
theorem original_id1147 : original1147.index = 1147 := by decide

def c1147 : Contract := original1147.toContract.get (by decide)
theorem binding1147 : original1147.toContract = some c1147 := rfl

theorem checked1147 : check 4000 c1147 = true := by decide

def original1148 : RawOriginal := C008.records[124]'(by decide)
theorem original_id1148 : original1148.index = 1148 := by decide

def c1148 : Contract := original1148.toContract.get (by decide)
theorem binding1148 : original1148.toContract = some c1148 := rfl

theorem checked1148 : check 4000 c1148 = true := by decide

def original1149 : RawOriginal := C008.records[125]'(by decide)
theorem original_id1149 : original1149.index = 1149 := by decide

def c1149 : Contract := original1149.toContract.get (by decide)
theorem binding1149 : original1149.toContract = some c1149 := rfl

theorem checked1149 : check 4000 c1149 = true := by decide

def original1150 : RawOriginal := C008.records[126]'(by decide)
theorem original_id1150 : original1150.index = 1150 := by decide

def c1150 : Contract := original1150.toContract.get (by decide)
theorem binding1150 : original1150.toContract = some c1150 := rfl

theorem checked1150 : check 4000 c1150 = true := by decide

def original1151 : RawOriginal := C008.records[127]'(by decide)
theorem original_id1151 : original1151.index = 1151 := by decide

def c1151 : Contract := original1151.toContract.get (by decide)
theorem binding1151 : original1151.toContract = some c1151 := rfl

theorem checked1151 : check 4000 c1151 = true := by decide

def original1152 : RawOriginal := C009.records[0]'(by decide)
theorem original_id1152 : original1152.index = 1152 := by decide

def c1152 : Contract := original1152.toContract.get (by decide)
theorem binding1152 : original1152.toContract = some c1152 := rfl

theorem checked1152 : check 4000 c1152 = true := by decide

def original1153 : RawOriginal := C009.records[1]'(by decide)
theorem original_id1153 : original1153.index = 1153 := by decide

def c1153 : Contract := original1153.toContract.get (by decide)
theorem binding1153 : original1153.toContract = some c1153 := rfl

theorem checked1153 : check 4000 c1153 = true := by decide

def original1154 : RawOriginal := C009.records[2]'(by decide)
theorem original_id1154 : original1154.index = 1154 := by decide

def c1154 : Contract := original1154.toContract.get (by decide)
theorem binding1154 : original1154.toContract = some c1154 := rfl

theorem checked1154 : check 4000 c1154 = true := by decide

def original1155 : RawOriginal := C009.records[3]'(by decide)
theorem original_id1155 : original1155.index = 1155 := by decide

def c1155 : Contract := original1155.toContract.get (by decide)
theorem binding1155 : original1155.toContract = some c1155 := rfl

theorem checked1155 : check 4000 c1155 = true := by decide

def original1156 : RawOriginal := C009.records[4]'(by decide)
theorem original_id1156 : original1156.index = 1156 := by decide

def c1156 : Contract := original1156.toContract.get (by decide)
theorem binding1156 : original1156.toContract = some c1156 := rfl

theorem checked1156 : check 4000 c1156 = true := by decide

def original1157 : RawOriginal := C009.records[5]'(by decide)
theorem original_id1157 : original1157.index = 1157 := by decide

def c1157 : Contract := original1157.toContract.get (by decide)
theorem binding1157 : original1157.toContract = some c1157 := rfl

theorem checked1157 : check 4000 c1157 = true := by decide

def records : List Certified := [
  ⟨1142, c1142, 4000, checked1142⟩,
  ⟨1143, c1143, 4000, checked1143⟩,
  ⟨1144, c1144, 4000, checked1144⟩,
  ⟨1145, c1145, 4000, checked1145⟩,
  ⟨1146, c1146, 4000, checked1146⟩,
  ⟨1147, c1147, 4000, checked1147⟩,
  ⟨1148, c1148, 4000, checked1148⟩,
  ⟨1149, c1149, 4000, checked1149⟩,
  ⟨1150, c1150, 4000, checked1150⟩,
  ⟨1151, c1151, 4000, checked1151⟩,
  ⟨1152, c1152, 4000, checked1152⟩,
  ⟨1153, c1153, 4000, checked1153⟩,
  ⟨1154, c1154, 4000, checked1154⟩,
  ⟨1155, c1155, 4000, checked1155⟩,
  ⟨1156, c1156, 4000, checked1156⟩,
  ⟨1157, c1157, 4000, checked1157⟩]

end PA215.ContractShards.Shard008Part7
