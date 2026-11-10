import PA215.CertifiedContracts
import PA215.Census.C010
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard010Part0
open PA215.Contracts PA215.Census

def original1286 : RawOriginal := C010.records[6]'(by decide)
theorem original_id1286 : original1286.index = 1286 := by decide

def c1286 : Contract := original1286.toContract.get (by decide)
theorem binding1286 : original1286.toContract = some c1286 := rfl

theorem checked1286 : check 4000 c1286 = true := by decide

def original1287 : RawOriginal := C010.records[7]'(by decide)
theorem original_id1287 : original1287.index = 1287 := by decide

def c1287 : Contract := original1287.toContract.get (by decide)
theorem binding1287 : original1287.toContract = some c1287 := rfl

theorem checked1287 : check 4000 c1287 = true := by decide

def original1288 : RawOriginal := C010.records[8]'(by decide)
theorem original_id1288 : original1288.index = 1288 := by decide

def c1288 : Contract := original1288.toContract.get (by decide)
theorem binding1288 : original1288.toContract = some c1288 := rfl

theorem checked1288 : check 4000 c1288 = true := by decide

def original1289 : RawOriginal := C010.records[9]'(by decide)
theorem original_id1289 : original1289.index = 1289 := by decide

def c1289 : Contract := original1289.toContract.get (by decide)
theorem binding1289 : original1289.toContract = some c1289 := rfl

theorem checked1289 : check 4000 c1289 = true := by decide

def original1290 : RawOriginal := C010.records[10]'(by decide)
theorem original_id1290 : original1290.index = 1290 := by decide

def c1290 : Contract := original1290.toContract.get (by decide)
theorem binding1290 : original1290.toContract = some c1290 := rfl

theorem checked1290 : check 4000 c1290 = true := by decide

def original1291 : RawOriginal := C010.records[11]'(by decide)
theorem original_id1291 : original1291.index = 1291 := by decide

def c1291 : Contract := original1291.toContract.get (by decide)
theorem binding1291 : original1291.toContract = some c1291 := rfl

theorem checked1291 : check 4000 c1291 = true := by decide

def original1292 : RawOriginal := C010.records[12]'(by decide)
theorem original_id1292 : original1292.index = 1292 := by decide

def c1292 : Contract := original1292.toContract.get (by decide)
theorem binding1292 : original1292.toContract = some c1292 := rfl

theorem checked1292 : check 4000 c1292 = true := by decide

def original1293 : RawOriginal := C010.records[13]'(by decide)
theorem original_id1293 : original1293.index = 1293 := by decide

def c1293 : Contract := original1293.toContract.get (by decide)
theorem binding1293 : original1293.toContract = some c1293 := rfl

theorem checked1293 : check 4000 c1293 = true := by decide

def original1294 : RawOriginal := C010.records[14]'(by decide)
theorem original_id1294 : original1294.index = 1294 := by decide

def c1294 : Contract := original1294.toContract.get (by decide)
theorem binding1294 : original1294.toContract = some c1294 := rfl

theorem checked1294 : check 4000 c1294 = true := by decide

def original1295 : RawOriginal := C010.records[15]'(by decide)
theorem original_id1295 : original1295.index = 1295 := by decide

def c1295 : Contract := original1295.toContract.get (by decide)
theorem binding1295 : original1295.toContract = some c1295 := rfl

theorem checked1295 : check 4000 c1295 = true := by decide

def original1296 : RawOriginal := C010.records[16]'(by decide)
theorem original_id1296 : original1296.index = 1296 := by decide

def c1296 : Contract := original1296.toContract.get (by decide)
theorem binding1296 : original1296.toContract = some c1296 := rfl

theorem checked1296 : check 4000 c1296 = true := by decide

def original1297 : RawOriginal := C010.records[17]'(by decide)
theorem original_id1297 : original1297.index = 1297 := by decide

def c1297 : Contract := original1297.toContract.get (by decide)
theorem binding1297 : original1297.toContract = some c1297 := rfl

theorem checked1297 : check 4000 c1297 = true := by decide

def original1298 : RawOriginal := C010.records[18]'(by decide)
theorem original_id1298 : original1298.index = 1298 := by decide

def c1298 : Contract := original1298.toContract.get (by decide)
theorem binding1298 : original1298.toContract = some c1298 := rfl

theorem checked1298 : check 4000 c1298 = true := by decide

def original1299 : RawOriginal := C010.records[19]'(by decide)
theorem original_id1299 : original1299.index = 1299 := by decide

def c1299 : Contract := original1299.toContract.get (by decide)
theorem binding1299 : original1299.toContract = some c1299 := rfl

theorem checked1299 : check 4000 c1299 = true := by decide

def original1300 : RawOriginal := C010.records[20]'(by decide)
theorem original_id1300 : original1300.index = 1300 := by decide

def c1300 : Contract := original1300.toContract.get (by decide)
theorem binding1300 : original1300.toContract = some c1300 := rfl

theorem checked1300 : check 4000 c1300 = true := by decide

def original1301 : RawOriginal := C010.records[21]'(by decide)
theorem original_id1301 : original1301.index = 1301 := by decide

def c1301 : Contract := original1301.toContract.get (by decide)
theorem binding1301 : original1301.toContract = some c1301 := rfl

theorem checked1301 : check 4000 c1301 = true := by decide

def records : List Certified := [
  ⟨1286, c1286, 4000, checked1286⟩,
  ⟨1287, c1287, 4000, checked1287⟩,
  ⟨1288, c1288, 4000, checked1288⟩,
  ⟨1289, c1289, 4000, checked1289⟩,
  ⟨1290, c1290, 4000, checked1290⟩,
  ⟨1291, c1291, 4000, checked1291⟩,
  ⟨1292, c1292, 4000, checked1292⟩,
  ⟨1293, c1293, 4000, checked1293⟩,
  ⟨1294, c1294, 4000, checked1294⟩,
  ⟨1295, c1295, 4000, checked1295⟩,
  ⟨1296, c1296, 4000, checked1296⟩,
  ⟨1297, c1297, 4000, checked1297⟩,
  ⟨1298, c1298, 4000, checked1298⟩,
  ⟨1299, c1299, 4000, checked1299⟩,
  ⟨1300, c1300, 4000, checked1300⟩,
  ⟨1301, c1301, 4000, checked1301⟩]

end PA215.ContractShards.Shard010Part0
