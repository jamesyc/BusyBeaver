import PA215.CertifiedContracts
import PA215.Census.C009
import PA215.Census.C010
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard009Part7
open PA215.Contracts PA215.Census

def original1270 : RawOriginal := C009.records[118]'(by decide)
theorem original_id1270 : original1270.index = 1270 := by decide

def c1270 : Contract := original1270.toContract.get (by decide)
theorem binding1270 : original1270.toContract = some c1270 := rfl

theorem checked1270 : check 4000 c1270 = true := by decide

def original1271 : RawOriginal := C009.records[119]'(by decide)
theorem original_id1271 : original1271.index = 1271 := by decide

def c1271 : Contract := original1271.toContract.get (by decide)
theorem binding1271 : original1271.toContract = some c1271 := rfl

theorem checked1271 : check 4000 c1271 = true := by decide

def original1272 : RawOriginal := C009.records[120]'(by decide)
theorem original_id1272 : original1272.index = 1272 := by decide

def c1272 : Contract := original1272.toContract.get (by decide)
theorem binding1272 : original1272.toContract = some c1272 := rfl

theorem checked1272 : check 4000 c1272 = true := by decide

def original1273 : RawOriginal := C009.records[121]'(by decide)
theorem original_id1273 : original1273.index = 1273 := by decide

def c1273 : Contract := original1273.toContract.get (by decide)
theorem binding1273 : original1273.toContract = some c1273 := rfl

theorem checked1273 : check 4000 c1273 = true := by decide

def original1274 : RawOriginal := C009.records[122]'(by decide)
theorem original_id1274 : original1274.index = 1274 := by decide

def c1274 : Contract := original1274.toContract.get (by decide)
theorem binding1274 : original1274.toContract = some c1274 := rfl

theorem checked1274 : check 4000 c1274 = true := by decide

def original1275 : RawOriginal := C009.records[123]'(by decide)
theorem original_id1275 : original1275.index = 1275 := by decide

def c1275 : Contract := original1275.toContract.get (by decide)
theorem binding1275 : original1275.toContract = some c1275 := rfl

theorem checked1275 : check 4000 c1275 = true := by decide

def original1276 : RawOriginal := C009.records[124]'(by decide)
theorem original_id1276 : original1276.index = 1276 := by decide

def c1276 : Contract := original1276.toContract.get (by decide)
theorem binding1276 : original1276.toContract = some c1276 := rfl

theorem checked1276 : check 4000 c1276 = true := by decide

def original1277 : RawOriginal := C009.records[125]'(by decide)
theorem original_id1277 : original1277.index = 1277 := by decide

def c1277 : Contract := original1277.toContract.get (by decide)
theorem binding1277 : original1277.toContract = some c1277 := rfl

theorem checked1277 : check 4000 c1277 = true := by decide

def original1278 : RawOriginal := C009.records[126]'(by decide)
theorem original_id1278 : original1278.index = 1278 := by decide

def c1278 : Contract := original1278.toContract.get (by decide)
theorem binding1278 : original1278.toContract = some c1278 := rfl

theorem checked1278 : check 4000 c1278 = true := by decide

def original1279 : RawOriginal := C009.records[127]'(by decide)
theorem original_id1279 : original1279.index = 1279 := by decide

def c1279 : Contract := original1279.toContract.get (by decide)
theorem binding1279 : original1279.toContract = some c1279 := rfl

theorem checked1279 : check 4000 c1279 = true := by decide

def original1280 : RawOriginal := C010.records[0]'(by decide)
theorem original_id1280 : original1280.index = 1280 := by decide

def c1280 : Contract := original1280.toContract.get (by decide)
theorem binding1280 : original1280.toContract = some c1280 := rfl

theorem checked1280 : check 4000 c1280 = true := by decide

def original1281 : RawOriginal := C010.records[1]'(by decide)
theorem original_id1281 : original1281.index = 1281 := by decide

def c1281 : Contract := original1281.toContract.get (by decide)
theorem binding1281 : original1281.toContract = some c1281 := rfl

theorem checked1281 : check 4000 c1281 = true := by decide

def original1282 : RawOriginal := C010.records[2]'(by decide)
theorem original_id1282 : original1282.index = 1282 := by decide

def c1282 : Contract := original1282.toContract.get (by decide)
theorem binding1282 : original1282.toContract = some c1282 := rfl

theorem checked1282 : check 4000 c1282 = true := by decide

def original1283 : RawOriginal := C010.records[3]'(by decide)
theorem original_id1283 : original1283.index = 1283 := by decide

def c1283 : Contract := original1283.toContract.get (by decide)
theorem binding1283 : original1283.toContract = some c1283 := rfl

theorem checked1283 : check 4000 c1283 = true := by decide

def original1284 : RawOriginal := C010.records[4]'(by decide)
theorem original_id1284 : original1284.index = 1284 := by decide

def c1284 : Contract := original1284.toContract.get (by decide)
theorem binding1284 : original1284.toContract = some c1284 := rfl

theorem checked1284 : check 4000 c1284 = true := by decide

def original1285 : RawOriginal := C010.records[5]'(by decide)
theorem original_id1285 : original1285.index = 1285 := by decide

def c1285 : Contract := original1285.toContract.get (by decide)
theorem binding1285 : original1285.toContract = some c1285 := rfl

theorem checked1285 : check 4000 c1285 = true := by decide

def records : List Certified := [
  ⟨1270, c1270, 4000, checked1270⟩,
  ⟨1271, c1271, 4000, checked1271⟩,
  ⟨1272, c1272, 4000, checked1272⟩,
  ⟨1273, c1273, 4000, checked1273⟩,
  ⟨1274, c1274, 4000, checked1274⟩,
  ⟨1275, c1275, 4000, checked1275⟩,
  ⟨1276, c1276, 4000, checked1276⟩,
  ⟨1277, c1277, 4000, checked1277⟩,
  ⟨1278, c1278, 4000, checked1278⟩,
  ⟨1279, c1279, 4000, checked1279⟩,
  ⟨1280, c1280, 4000, checked1280⟩,
  ⟨1281, c1281, 4000, checked1281⟩,
  ⟨1282, c1282, 4000, checked1282⟩,
  ⟨1283, c1283, 4000, checked1283⟩,
  ⟨1284, c1284, 4000, checked1284⟩,
  ⟨1285, c1285, 4000, checked1285⟩]

end PA215.ContractShards.Shard009Part7
