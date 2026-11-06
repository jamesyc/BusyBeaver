import PA215.CertifiedContracts
import PA215.Census.C010
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard010Part4
open PA215.Contracts PA215.Census

def original1350 : RawOriginal := C010.records[70]'(by decide)
theorem original_id1350 : original1350.index = 1350 := by decide

def c1350 : Contract := original1350.toContract.get (by decide)
theorem binding1350 : original1350.toContract = some c1350 := rfl

theorem checked1350 : check 4000 c1350 = true := by decide

def original1351 : RawOriginal := C010.records[71]'(by decide)
theorem original_id1351 : original1351.index = 1351 := by decide

def c1351 : Contract := original1351.toContract.get (by decide)
theorem binding1351 : original1351.toContract = some c1351 := rfl

theorem checked1351 : check 4000 c1351 = true := by decide

def original1352 : RawOriginal := C010.records[72]'(by decide)
theorem original_id1352 : original1352.index = 1352 := by decide

def c1352 : Contract := original1352.toContract.get (by decide)
theorem binding1352 : original1352.toContract = some c1352 := rfl

theorem checked1352 : check 4000 c1352 = true := by decide

def original1353 : RawOriginal := C010.records[73]'(by decide)
theorem original_id1353 : original1353.index = 1353 := by decide

def c1353 : Contract := original1353.toContract.get (by decide)
theorem binding1353 : original1353.toContract = some c1353 := rfl

theorem checked1353 : check 4000 c1353 = true := by decide

def original1354 : RawOriginal := C010.records[74]'(by decide)
theorem original_id1354 : original1354.index = 1354 := by decide

def c1354 : Contract := original1354.toContract.get (by decide)
theorem binding1354 : original1354.toContract = some c1354 := rfl

theorem checked1354 : check 4000 c1354 = true := by decide

def original1355 : RawOriginal := C010.records[75]'(by decide)
theorem original_id1355 : original1355.index = 1355 := by decide

def c1355 : Contract := original1355.toContract.get (by decide)
theorem binding1355 : original1355.toContract = some c1355 := rfl

theorem checked1355 : check 4000 c1355 = true := by decide

def original1356 : RawOriginal := C010.records[76]'(by decide)
theorem original_id1356 : original1356.index = 1356 := by decide

def c1356 : Contract := original1356.toContract.get (by decide)
theorem binding1356 : original1356.toContract = some c1356 := rfl

theorem checked1356 : check 4000 c1356 = true := by decide

def original1357 : RawOriginal := C010.records[77]'(by decide)
theorem original_id1357 : original1357.index = 1357 := by decide

def c1357 : Contract := original1357.toContract.get (by decide)
theorem binding1357 : original1357.toContract = some c1357 := rfl

theorem checked1357 : check 4000 c1357 = true := by decide

def original1358 : RawOriginal := C010.records[78]'(by decide)
theorem original_id1358 : original1358.index = 1358 := by decide

def c1358 : Contract := original1358.toContract.get (by decide)
theorem binding1358 : original1358.toContract = some c1358 := rfl

theorem checked1358 : check 4000 c1358 = true := by decide

def original1359 : RawOriginal := C010.records[79]'(by decide)
theorem original_id1359 : original1359.index = 1359 := by decide

def c1359 : Contract := original1359.toContract.get (by decide)
theorem binding1359 : original1359.toContract = some c1359 := rfl

theorem checked1359 : check 4000 c1359 = true := by decide

def original1360 : RawOriginal := C010.records[80]'(by decide)
theorem original_id1360 : original1360.index = 1360 := by decide

def c1360 : Contract := original1360.toContract.get (by decide)
theorem binding1360 : original1360.toContract = some c1360 := rfl

theorem checked1360 : check 4000 c1360 = true := by decide

def original1361 : RawOriginal := C010.records[81]'(by decide)
theorem original_id1361 : original1361.index = 1361 := by decide

def c1361 : Contract := original1361.toContract.get (by decide)
theorem binding1361 : original1361.toContract = some c1361 := rfl

theorem checked1361 : check 4000 c1361 = true := by decide

def original1362 : RawOriginal := C010.records[82]'(by decide)
theorem original_id1362 : original1362.index = 1362 := by decide

def c1362 : Contract := original1362.toContract.get (by decide)
theorem binding1362 : original1362.toContract = some c1362 := rfl

theorem checked1362 : check 4000 c1362 = true := by decide

def original1363 : RawOriginal := C010.records[83]'(by decide)
theorem original_id1363 : original1363.index = 1363 := by decide

def c1363 : Contract := original1363.toContract.get (by decide)
theorem binding1363 : original1363.toContract = some c1363 := rfl

theorem checked1363 : check 4000 c1363 = true := by decide

def original1364 : RawOriginal := C010.records[84]'(by decide)
theorem original_id1364 : original1364.index = 1364 := by decide

def c1364 : Contract := original1364.toContract.get (by decide)
theorem binding1364 : original1364.toContract = some c1364 := rfl

theorem checked1364 : check 4000 c1364 = true := by decide

def original1365 : RawOriginal := C010.records[85]'(by decide)
theorem original_id1365 : original1365.index = 1365 := by decide

def c1365 : Contract := original1365.toContract.get (by decide)
theorem binding1365 : original1365.toContract = some c1365 := rfl

theorem checked1365 : check 4000 c1365 = true := by decide

def records : List Certified := [
  ⟨1350, c1350, 4000, checked1350⟩,
  ⟨1351, c1351, 4000, checked1351⟩,
  ⟨1352, c1352, 4000, checked1352⟩,
  ⟨1353, c1353, 4000, checked1353⟩,
  ⟨1354, c1354, 4000, checked1354⟩,
  ⟨1355, c1355, 4000, checked1355⟩,
  ⟨1356, c1356, 4000, checked1356⟩,
  ⟨1357, c1357, 4000, checked1357⟩,
  ⟨1358, c1358, 4000, checked1358⟩,
  ⟨1359, c1359, 4000, checked1359⟩,
  ⟨1360, c1360, 4000, checked1360⟩,
  ⟨1361, c1361, 4000, checked1361⟩,
  ⟨1362, c1362, 4000, checked1362⟩,
  ⟨1363, c1363, 4000, checked1363⟩,
  ⟨1364, c1364, 4000, checked1364⟩,
  ⟨1365, c1365, 4000, checked1365⟩]

end PA215.ContractShards.Shard010Part4
