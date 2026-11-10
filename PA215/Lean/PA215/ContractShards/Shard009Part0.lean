import PA215.CertifiedContracts
import PA215.Census.C009
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard009Part0
open PA215.Contracts PA215.Census

def original1158 : RawOriginal := C009.records[6]'(by decide)
theorem original_id1158 : original1158.index = 1158 := by decide

def c1158 : Contract := original1158.toContract.get (by decide)
theorem binding1158 : original1158.toContract = some c1158 := rfl

theorem checked1158 : check 4000 c1158 = true := by decide

def original1159 : RawOriginal := C009.records[7]'(by decide)
theorem original_id1159 : original1159.index = 1159 := by decide

def c1159 : Contract := original1159.toContract.get (by decide)
theorem binding1159 : original1159.toContract = some c1159 := rfl

theorem checked1159 : check 4000 c1159 = true := by decide

def original1160 : RawOriginal := C009.records[8]'(by decide)
theorem original_id1160 : original1160.index = 1160 := by decide

def c1160 : Contract := original1160.toContract.get (by decide)
theorem binding1160 : original1160.toContract = some c1160 := rfl

theorem checked1160 : check 4000 c1160 = true := by decide

def original1161 : RawOriginal := C009.records[9]'(by decide)
theorem original_id1161 : original1161.index = 1161 := by decide

def c1161 : Contract := original1161.toContract.get (by decide)
theorem binding1161 : original1161.toContract = some c1161 := rfl

theorem checked1161 : check 4000 c1161 = true := by decide

def original1162 : RawOriginal := C009.records[10]'(by decide)
theorem original_id1162 : original1162.index = 1162 := by decide

def c1162 : Contract := original1162.toContract.get (by decide)
theorem binding1162 : original1162.toContract = some c1162 := rfl

theorem checked1162 : check 4000 c1162 = true := by decide

def original1163 : RawOriginal := C009.records[11]'(by decide)
theorem original_id1163 : original1163.index = 1163 := by decide

def c1163 : Contract := original1163.toContract.get (by decide)
theorem binding1163 : original1163.toContract = some c1163 := rfl

theorem checked1163 : check 4000 c1163 = true := by decide

def original1164 : RawOriginal := C009.records[12]'(by decide)
theorem original_id1164 : original1164.index = 1164 := by decide

def c1164 : Contract := original1164.toContract.get (by decide)
theorem binding1164 : original1164.toContract = some c1164 := rfl

theorem checked1164 : check 4000 c1164 = true := by decide

def original1165 : RawOriginal := C009.records[13]'(by decide)
theorem original_id1165 : original1165.index = 1165 := by decide

def c1165 : Contract := original1165.toContract.get (by decide)
theorem binding1165 : original1165.toContract = some c1165 := rfl

theorem checked1165 : check 4000 c1165 = true := by decide

def original1166 : RawOriginal := C009.records[14]'(by decide)
theorem original_id1166 : original1166.index = 1166 := by decide

def c1166 : Contract := original1166.toContract.get (by decide)
theorem binding1166 : original1166.toContract = some c1166 := rfl

theorem checked1166 : check 4000 c1166 = true := by decide

def original1167 : RawOriginal := C009.records[15]'(by decide)
theorem original_id1167 : original1167.index = 1167 := by decide

def c1167 : Contract := original1167.toContract.get (by decide)
theorem binding1167 : original1167.toContract = some c1167 := rfl

theorem checked1167 : check 4000 c1167 = true := by decide

def original1168 : RawOriginal := C009.records[16]'(by decide)
theorem original_id1168 : original1168.index = 1168 := by decide

def c1168 : Contract := original1168.toContract.get (by decide)
theorem binding1168 : original1168.toContract = some c1168 := rfl

theorem checked1168 : check 4000 c1168 = true := by decide

def original1169 : RawOriginal := C009.records[17]'(by decide)
theorem original_id1169 : original1169.index = 1169 := by decide

def c1169 : Contract := original1169.toContract.get (by decide)
theorem binding1169 : original1169.toContract = some c1169 := rfl

theorem checked1169 : check 4000 c1169 = true := by decide

def original1170 : RawOriginal := C009.records[18]'(by decide)
theorem original_id1170 : original1170.index = 1170 := by decide

def c1170 : Contract := original1170.toContract.get (by decide)
theorem binding1170 : original1170.toContract = some c1170 := rfl

theorem checked1170 : check 4000 c1170 = true := by decide

def original1171 : RawOriginal := C009.records[19]'(by decide)
theorem original_id1171 : original1171.index = 1171 := by decide

def c1171 : Contract := original1171.toContract.get (by decide)
theorem binding1171 : original1171.toContract = some c1171 := rfl

theorem checked1171 : check 4000 c1171 = true := by decide

def original1172 : RawOriginal := C009.records[20]'(by decide)
theorem original_id1172 : original1172.index = 1172 := by decide

def c1172 : Contract := original1172.toContract.get (by decide)
theorem binding1172 : original1172.toContract = some c1172 := rfl

theorem checked1172 : check 4000 c1172 = true := by decide

def original1173 : RawOriginal := C009.records[21]'(by decide)
theorem original_id1173 : original1173.index = 1173 := by decide

def c1173 : Contract := original1173.toContract.get (by decide)
theorem binding1173 : original1173.toContract = some c1173 := rfl

theorem checked1173 : check 4000 c1173 = true := by decide

def records : List Certified := [
  ⟨1158, c1158, 4000, checked1158⟩,
  ⟨1159, c1159, 4000, checked1159⟩,
  ⟨1160, c1160, 4000, checked1160⟩,
  ⟨1161, c1161, 4000, checked1161⟩,
  ⟨1162, c1162, 4000, checked1162⟩,
  ⟨1163, c1163, 4000, checked1163⟩,
  ⟨1164, c1164, 4000, checked1164⟩,
  ⟨1165, c1165, 4000, checked1165⟩,
  ⟨1166, c1166, 4000, checked1166⟩,
  ⟨1167, c1167, 4000, checked1167⟩,
  ⟨1168, c1168, 4000, checked1168⟩,
  ⟨1169, c1169, 4000, checked1169⟩,
  ⟨1170, c1170, 4000, checked1170⟩,
  ⟨1171, c1171, 4000, checked1171⟩,
  ⟨1172, c1172, 4000, checked1172⟩,
  ⟨1173, c1173, 4000, checked1173⟩]

end PA215.ContractShards.Shard009Part0
