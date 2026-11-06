import PA215.CertifiedContracts
import PA215.Census.C009
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard009Part3
open PA215.Contracts PA215.Census

def original1206 : RawOriginal := C009.records[54]'(by decide)
theorem original_id1206 : original1206.index = 1206 := by decide

def c1206 : Contract := original1206.toContract.get (by decide)
theorem binding1206 : original1206.toContract = some c1206 := rfl

theorem checked1206 : check 4000 c1206 = true := by decide

def original1207 : RawOriginal := C009.records[55]'(by decide)
theorem original_id1207 : original1207.index = 1207 := by decide

def c1207 : Contract := original1207.toContract.get (by decide)
theorem binding1207 : original1207.toContract = some c1207 := rfl

theorem checked1207 : check 4000 c1207 = true := by decide

def original1208 : RawOriginal := C009.records[56]'(by decide)
theorem original_id1208 : original1208.index = 1208 := by decide

def c1208 : Contract := original1208.toContract.get (by decide)
theorem binding1208 : original1208.toContract = some c1208 := rfl

theorem checked1208 : check 4000 c1208 = true := by decide

def original1209 : RawOriginal := C009.records[57]'(by decide)
theorem original_id1209 : original1209.index = 1209 := by decide

def c1209 : Contract := original1209.toContract.get (by decide)
theorem binding1209 : original1209.toContract = some c1209 := rfl

theorem checked1209 : check 4000 c1209 = true := by decide

def original1210 : RawOriginal := C009.records[58]'(by decide)
theorem original_id1210 : original1210.index = 1210 := by decide

def c1210 : Contract := original1210.toContract.get (by decide)
theorem binding1210 : original1210.toContract = some c1210 := rfl

theorem checked1210 : check 4000 c1210 = true := by decide

def original1211 : RawOriginal := C009.records[59]'(by decide)
theorem original_id1211 : original1211.index = 1211 := by decide

def c1211 : Contract := original1211.toContract.get (by decide)
theorem binding1211 : original1211.toContract = some c1211 := rfl

theorem checked1211 : check 4000 c1211 = true := by decide

def original1212 : RawOriginal := C009.records[60]'(by decide)
theorem original_id1212 : original1212.index = 1212 := by decide

def c1212 : Contract := original1212.toContract.get (by decide)
theorem binding1212 : original1212.toContract = some c1212 := rfl

theorem checked1212 : check 4000 c1212 = true := by decide

def original1213 : RawOriginal := C009.records[61]'(by decide)
theorem original_id1213 : original1213.index = 1213 := by decide

def c1213 : Contract := original1213.toContract.get (by decide)
theorem binding1213 : original1213.toContract = some c1213 := rfl

theorem checked1213 : check 4000 c1213 = true := by decide

def original1214 : RawOriginal := C009.records[62]'(by decide)
theorem original_id1214 : original1214.index = 1214 := by decide

def c1214 : Contract := original1214.toContract.get (by decide)
theorem binding1214 : original1214.toContract = some c1214 := rfl

theorem checked1214 : check 4000 c1214 = true := by decide

def original1215 : RawOriginal := C009.records[63]'(by decide)
theorem original_id1215 : original1215.index = 1215 := by decide

def c1215 : Contract := original1215.toContract.get (by decide)
theorem binding1215 : original1215.toContract = some c1215 := rfl

theorem checked1215 : check 4000 c1215 = true := by decide

def original1216 : RawOriginal := C009.records[64]'(by decide)
theorem original_id1216 : original1216.index = 1216 := by decide

def c1216 : Contract := original1216.toContract.get (by decide)
theorem binding1216 : original1216.toContract = some c1216 := rfl

theorem checked1216 : check 4000 c1216 = true := by decide

def original1217 : RawOriginal := C009.records[65]'(by decide)
theorem original_id1217 : original1217.index = 1217 := by decide

def c1217 : Contract := original1217.toContract.get (by decide)
theorem binding1217 : original1217.toContract = some c1217 := rfl

theorem checked1217 : check 4000 c1217 = true := by decide

def original1218 : RawOriginal := C009.records[66]'(by decide)
theorem original_id1218 : original1218.index = 1218 := by decide

def c1218 : Contract := original1218.toContract.get (by decide)
theorem binding1218 : original1218.toContract = some c1218 := rfl

theorem checked1218 : check 4000 c1218 = true := by decide

def original1219 : RawOriginal := C009.records[67]'(by decide)
theorem original_id1219 : original1219.index = 1219 := by decide

def c1219 : Contract := original1219.toContract.get (by decide)
theorem binding1219 : original1219.toContract = some c1219 := rfl

theorem checked1219 : check 4000 c1219 = true := by decide

def original1220 : RawOriginal := C009.records[68]'(by decide)
theorem original_id1220 : original1220.index = 1220 := by decide

def c1220 : Contract := original1220.toContract.get (by decide)
theorem binding1220 : original1220.toContract = some c1220 := rfl

theorem checked1220 : check 4000 c1220 = true := by decide

def original1221 : RawOriginal := C009.records[69]'(by decide)
theorem original_id1221 : original1221.index = 1221 := by decide

def c1221 : Contract := original1221.toContract.get (by decide)
theorem binding1221 : original1221.toContract = some c1221 := rfl

theorem checked1221 : check 4000 c1221 = true := by decide

def records : List Certified := [
  ⟨1206, c1206, 4000, checked1206⟩,
  ⟨1207, c1207, 4000, checked1207⟩,
  ⟨1208, c1208, 4000, checked1208⟩,
  ⟨1209, c1209, 4000, checked1209⟩,
  ⟨1210, c1210, 4000, checked1210⟩,
  ⟨1211, c1211, 4000, checked1211⟩,
  ⟨1212, c1212, 4000, checked1212⟩,
  ⟨1213, c1213, 4000, checked1213⟩,
  ⟨1214, c1214, 4000, checked1214⟩,
  ⟨1215, c1215, 4000, checked1215⟩,
  ⟨1216, c1216, 4000, checked1216⟩,
  ⟨1217, c1217, 4000, checked1217⟩,
  ⟨1218, c1218, 4000, checked1218⟩,
  ⟨1219, c1219, 4000, checked1219⟩,
  ⟨1220, c1220, 4000, checked1220⟩,
  ⟨1221, c1221, 4000, checked1221⟩]

end PA215.ContractShards.Shard009Part3
