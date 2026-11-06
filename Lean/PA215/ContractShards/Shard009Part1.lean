import PA215.CertifiedContracts
import PA215.Census.C009
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard009Part1
open PA215.Contracts PA215.Census

def original1174 : RawOriginal := C009.records[22]'(by decide)
theorem original_id1174 : original1174.index = 1174 := by decide

def c1174 : Contract := original1174.toContract.get (by decide)
theorem binding1174 : original1174.toContract = some c1174 := rfl

theorem checked1174 : check 4000 c1174 = true := by decide

def original1175 : RawOriginal := C009.records[23]'(by decide)
theorem original_id1175 : original1175.index = 1175 := by decide

def c1175 : Contract := original1175.toContract.get (by decide)
theorem binding1175 : original1175.toContract = some c1175 := rfl

theorem checked1175 : check 4000 c1175 = true := by decide

def original1176 : RawOriginal := C009.records[24]'(by decide)
theorem original_id1176 : original1176.index = 1176 := by decide

def c1176 : Contract := original1176.toContract.get (by decide)
theorem binding1176 : original1176.toContract = some c1176 := rfl

theorem checked1176 : check 4000 c1176 = true := by decide

def original1177 : RawOriginal := C009.records[25]'(by decide)
theorem original_id1177 : original1177.index = 1177 := by decide

def c1177 : Contract := original1177.toContract.get (by decide)
theorem binding1177 : original1177.toContract = some c1177 := rfl

theorem checked1177 : check 4000 c1177 = true := by decide

def original1178 : RawOriginal := C009.records[26]'(by decide)
theorem original_id1178 : original1178.index = 1178 := by decide

def c1178 : Contract := original1178.toContract.get (by decide)
theorem binding1178 : original1178.toContract = some c1178 := rfl

theorem checked1178 : check 4000 c1178 = true := by decide

def original1179 : RawOriginal := C009.records[27]'(by decide)
theorem original_id1179 : original1179.index = 1179 := by decide

def c1179 : Contract := original1179.toContract.get (by decide)
theorem binding1179 : original1179.toContract = some c1179 := rfl

theorem checked1179 : check 4000 c1179 = true := by decide

def original1180 : RawOriginal := C009.records[28]'(by decide)
theorem original_id1180 : original1180.index = 1180 := by decide

def c1180 : Contract := original1180.toContract.get (by decide)
theorem binding1180 : original1180.toContract = some c1180 := rfl

theorem checked1180 : check 4000 c1180 = true := by decide

def original1181 : RawOriginal := C009.records[29]'(by decide)
theorem original_id1181 : original1181.index = 1181 := by decide

def c1181 : Contract := original1181.toContract.get (by decide)
theorem binding1181 : original1181.toContract = some c1181 := rfl

theorem checked1181 : check 4000 c1181 = true := by decide

def original1182 : RawOriginal := C009.records[30]'(by decide)
theorem original_id1182 : original1182.index = 1182 := by decide

def c1182 : Contract := original1182.toContract.get (by decide)
theorem binding1182 : original1182.toContract = some c1182 := rfl

theorem checked1182 : check 4000 c1182 = true := by decide

def original1183 : RawOriginal := C009.records[31]'(by decide)
theorem original_id1183 : original1183.index = 1183 := by decide

def c1183 : Contract := original1183.toContract.get (by decide)
theorem binding1183 : original1183.toContract = some c1183 := rfl

theorem checked1183 : check 4000 c1183 = true := by decide

def original1184 : RawOriginal := C009.records[32]'(by decide)
theorem original_id1184 : original1184.index = 1184 := by decide

def c1184 : Contract := original1184.toContract.get (by decide)
theorem binding1184 : original1184.toContract = some c1184 := rfl

theorem checked1184 : check 4000 c1184 = true := by decide

def original1185 : RawOriginal := C009.records[33]'(by decide)
theorem original_id1185 : original1185.index = 1185 := by decide

def c1185 : Contract := original1185.toContract.get (by decide)
theorem binding1185 : original1185.toContract = some c1185 := rfl

theorem checked1185 : check 4000 c1185 = true := by decide

def original1186 : RawOriginal := C009.records[34]'(by decide)
theorem original_id1186 : original1186.index = 1186 := by decide

def c1186 : Contract := original1186.toContract.get (by decide)
theorem binding1186 : original1186.toContract = some c1186 := rfl

theorem checked1186 : check 4000 c1186 = true := by decide

def original1187 : RawOriginal := C009.records[35]'(by decide)
theorem original_id1187 : original1187.index = 1187 := by decide

def c1187 : Contract := original1187.toContract.get (by decide)
theorem binding1187 : original1187.toContract = some c1187 := rfl

theorem checked1187 : check 4000 c1187 = true := by decide

def original1188 : RawOriginal := C009.records[36]'(by decide)
theorem original_id1188 : original1188.index = 1188 := by decide

def c1188 : Contract := original1188.toContract.get (by decide)
theorem binding1188 : original1188.toContract = some c1188 := rfl

theorem checked1188 : check 4000 c1188 = true := by decide

def original1189 : RawOriginal := C009.records[37]'(by decide)
theorem original_id1189 : original1189.index = 1189 := by decide

def c1189 : Contract := original1189.toContract.get (by decide)
theorem binding1189 : original1189.toContract = some c1189 := rfl

theorem checked1189 : check 4000 c1189 = true := by decide

def records : List Certified := [
  ⟨1174, c1174, 4000, checked1174⟩,
  ⟨1175, c1175, 4000, checked1175⟩,
  ⟨1176, c1176, 4000, checked1176⟩,
  ⟨1177, c1177, 4000, checked1177⟩,
  ⟨1178, c1178, 4000, checked1178⟩,
  ⟨1179, c1179, 4000, checked1179⟩,
  ⟨1180, c1180, 4000, checked1180⟩,
  ⟨1181, c1181, 4000, checked1181⟩,
  ⟨1182, c1182, 4000, checked1182⟩,
  ⟨1183, c1183, 4000, checked1183⟩,
  ⟨1184, c1184, 4000, checked1184⟩,
  ⟨1185, c1185, 4000, checked1185⟩,
  ⟨1186, c1186, 4000, checked1186⟩,
  ⟨1187, c1187, 4000, checked1187⟩,
  ⟨1188, c1188, 4000, checked1188⟩,
  ⟨1189, c1189, 4000, checked1189⟩]

end PA215.ContractShards.Shard009Part1
