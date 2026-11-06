import PA215.CertifiedContracts
import PA215.Census.C009
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard009Part5
open PA215.Contracts PA215.Census

def original1238 : RawOriginal := C009.records[86]'(by decide)
theorem original_id1238 : original1238.index = 1238 := by decide

def c1238 : Contract := original1238.toContract.get (by decide)
theorem binding1238 : original1238.toContract = some c1238 := rfl

theorem checked1238 : check 4000 c1238 = true := by decide

def original1239 : RawOriginal := C009.records[87]'(by decide)
theorem original_id1239 : original1239.index = 1239 := by decide

def c1239 : Contract := original1239.toContract.get (by decide)
theorem binding1239 : original1239.toContract = some c1239 := rfl

theorem checked1239 : check 4000 c1239 = true := by decide

def original1240 : RawOriginal := C009.records[88]'(by decide)
theorem original_id1240 : original1240.index = 1240 := by decide

def c1240 : Contract := original1240.toContract.get (by decide)
theorem binding1240 : original1240.toContract = some c1240 := rfl

theorem checked1240 : check 4000 c1240 = true := by decide

def original1241 : RawOriginal := C009.records[89]'(by decide)
theorem original_id1241 : original1241.index = 1241 := by decide

def c1241 : Contract := original1241.toContract.get (by decide)
theorem binding1241 : original1241.toContract = some c1241 := rfl

theorem checked1241 : check 4000 c1241 = true := by decide

def original1242 : RawOriginal := C009.records[90]'(by decide)
theorem original_id1242 : original1242.index = 1242 := by decide

def c1242 : Contract := original1242.toContract.get (by decide)
theorem binding1242 : original1242.toContract = some c1242 := rfl

theorem checked1242 : check 4000 c1242 = true := by decide

def original1243 : RawOriginal := C009.records[91]'(by decide)
theorem original_id1243 : original1243.index = 1243 := by decide

def c1243 : Contract := original1243.toContract.get (by decide)
theorem binding1243 : original1243.toContract = some c1243 := rfl

theorem checked1243 : check 4000 c1243 = true := by decide

def original1244 : RawOriginal := C009.records[92]'(by decide)
theorem original_id1244 : original1244.index = 1244 := by decide

def c1244 : Contract := original1244.toContract.get (by decide)
theorem binding1244 : original1244.toContract = some c1244 := rfl

theorem checked1244 : check 4000 c1244 = true := by decide

def original1245 : RawOriginal := C009.records[93]'(by decide)
theorem original_id1245 : original1245.index = 1245 := by decide

def c1245 : Contract := original1245.toContract.get (by decide)
theorem binding1245 : original1245.toContract = some c1245 := rfl

theorem checked1245 : check 4000 c1245 = true := by decide

def original1246 : RawOriginal := C009.records[94]'(by decide)
theorem original_id1246 : original1246.index = 1246 := by decide

def c1246 : Contract := original1246.toContract.get (by decide)
theorem binding1246 : original1246.toContract = some c1246 := rfl

theorem checked1246 : check 4000 c1246 = true := by decide

def original1247 : RawOriginal := C009.records[95]'(by decide)
theorem original_id1247 : original1247.index = 1247 := by decide

def c1247 : Contract := original1247.toContract.get (by decide)
theorem binding1247 : original1247.toContract = some c1247 := rfl

theorem checked1247 : check 4000 c1247 = true := by decide

def original1248 : RawOriginal := C009.records[96]'(by decide)
theorem original_id1248 : original1248.index = 1248 := by decide

def c1248 : Contract := original1248.toContract.get (by decide)
theorem binding1248 : original1248.toContract = some c1248 := rfl

theorem checked1248 : check 4000 c1248 = true := by decide

def original1249 : RawOriginal := C009.records[97]'(by decide)
theorem original_id1249 : original1249.index = 1249 := by decide

def c1249 : Contract := original1249.toContract.get (by decide)
theorem binding1249 : original1249.toContract = some c1249 := rfl

theorem checked1249 : check 4000 c1249 = true := by decide

def original1250 : RawOriginal := C009.records[98]'(by decide)
theorem original_id1250 : original1250.index = 1250 := by decide

def c1250 : Contract := original1250.toContract.get (by decide)
theorem binding1250 : original1250.toContract = some c1250 := rfl

theorem checked1250 : check 4000 c1250 = true := by decide

def original1251 : RawOriginal := C009.records[99]'(by decide)
theorem original_id1251 : original1251.index = 1251 := by decide

def c1251 : Contract := original1251.toContract.get (by decide)
theorem binding1251 : original1251.toContract = some c1251 := rfl

theorem checked1251 : check 4000 c1251 = true := by decide

def original1252 : RawOriginal := C009.records[100]'(by decide)
theorem original_id1252 : original1252.index = 1252 := by decide

def c1252 : Contract := original1252.toContract.get (by decide)
theorem binding1252 : original1252.toContract = some c1252 := rfl

theorem checked1252 : check 4000 c1252 = true := by decide

def original1253 : RawOriginal := C009.records[101]'(by decide)
theorem original_id1253 : original1253.index = 1253 := by decide

def c1253 : Contract := original1253.toContract.get (by decide)
theorem binding1253 : original1253.toContract = some c1253 := rfl

theorem checked1253 : check 4000 c1253 = true := by decide

def records : List Certified := [
  ⟨1238, c1238, 4000, checked1238⟩,
  ⟨1239, c1239, 4000, checked1239⟩,
  ⟨1240, c1240, 4000, checked1240⟩,
  ⟨1241, c1241, 4000, checked1241⟩,
  ⟨1242, c1242, 4000, checked1242⟩,
  ⟨1243, c1243, 4000, checked1243⟩,
  ⟨1244, c1244, 4000, checked1244⟩,
  ⟨1245, c1245, 4000, checked1245⟩,
  ⟨1246, c1246, 4000, checked1246⟩,
  ⟨1247, c1247, 4000, checked1247⟩,
  ⟨1248, c1248, 4000, checked1248⟩,
  ⟨1249, c1249, 4000, checked1249⟩,
  ⟨1250, c1250, 4000, checked1250⟩,
  ⟨1251, c1251, 4000, checked1251⟩,
  ⟨1252, c1252, 4000, checked1252⟩,
  ⟨1253, c1253, 4000, checked1253⟩]

end PA215.ContractShards.Shard009Part5
