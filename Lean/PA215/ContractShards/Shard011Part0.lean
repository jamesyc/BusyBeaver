import PA215.CertifiedContracts
import PA215.Census.C011
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard011Part0
open PA215.Contracts PA215.Census

def original1414 : RawOriginal := C011.records[6]'(by decide)
theorem original_id1414 : original1414.index = 1414 := by decide

def c1414 : Contract := original1414.toContract.get (by decide)
theorem binding1414 : original1414.toContract = some c1414 := rfl

theorem checked1414 : check 4000 c1414 = true := by decide

def original1415 : RawOriginal := C011.records[7]'(by decide)
theorem original_id1415 : original1415.index = 1415 := by decide

def c1415 : Contract := original1415.toContract.get (by decide)
theorem binding1415 : original1415.toContract = some c1415 := rfl

theorem checked1415 : check 4000 c1415 = true := by decide

def original1416 : RawOriginal := C011.records[8]'(by decide)
theorem original_id1416 : original1416.index = 1416 := by decide

def c1416 : Contract := original1416.toContract.get (by decide)
theorem binding1416 : original1416.toContract = some c1416 := rfl

theorem checked1416 : check 4000 c1416 = true := by decide

def original1417 : RawOriginal := C011.records[9]'(by decide)
theorem original_id1417 : original1417.index = 1417 := by decide

def c1417 : Contract := original1417.toContract.get (by decide)
theorem binding1417 : original1417.toContract = some c1417 := rfl

theorem checked1417 : check 4000 c1417 = true := by decide

def original1418 : RawOriginal := C011.records[10]'(by decide)
theorem original_id1418 : original1418.index = 1418 := by decide

def c1418 : Contract := original1418.toContract.get (by decide)
theorem binding1418 : original1418.toContract = some c1418 := rfl

theorem checked1418 : check 4000 c1418 = true := by decide

def original1419 : RawOriginal := C011.records[11]'(by decide)
theorem original_id1419 : original1419.index = 1419 := by decide

def c1419 : Contract := original1419.toContract.get (by decide)
theorem binding1419 : original1419.toContract = some c1419 := rfl

theorem checked1419 : check 4000 c1419 = true := by decide

def original1420 : RawOriginal := C011.records[12]'(by decide)
theorem original_id1420 : original1420.index = 1420 := by decide

def c1420 : Contract := original1420.toContract.get (by decide)
theorem binding1420 : original1420.toContract = some c1420 := rfl

theorem checked1420 : check 4000 c1420 = true := by decide

def original1421 : RawOriginal := C011.records[13]'(by decide)
theorem original_id1421 : original1421.index = 1421 := by decide

def c1421 : Contract := original1421.toContract.get (by decide)
theorem binding1421 : original1421.toContract = some c1421 := rfl

theorem checked1421 : check 4000 c1421 = true := by decide

def original1422 : RawOriginal := C011.records[14]'(by decide)
theorem original_id1422 : original1422.index = 1422 := by decide

def c1422 : Contract := original1422.toContract.get (by decide)
theorem binding1422 : original1422.toContract = some c1422 := rfl

theorem checked1422 : check 4000 c1422 = true := by decide

def original1423 : RawOriginal := C011.records[15]'(by decide)
theorem original_id1423 : original1423.index = 1423 := by decide

def c1423 : Contract := original1423.toContract.get (by decide)
theorem binding1423 : original1423.toContract = some c1423 := rfl

theorem checked1423 : check 4000 c1423 = true := by decide

def original1424 : RawOriginal := C011.records[16]'(by decide)
theorem original_id1424 : original1424.index = 1424 := by decide

def c1424 : Contract := original1424.toContract.get (by decide)
theorem binding1424 : original1424.toContract = some c1424 := rfl

theorem checked1424 : check 4000 c1424 = true := by decide

def original1425 : RawOriginal := C011.records[17]'(by decide)
theorem original_id1425 : original1425.index = 1425 := by decide

def c1425 : Contract := original1425.toContract.get (by decide)
theorem binding1425 : original1425.toContract = some c1425 := rfl

theorem checked1425 : check 4000 c1425 = true := by decide

def original1426 : RawOriginal := C011.records[18]'(by decide)
theorem original_id1426 : original1426.index = 1426 := by decide

def c1426 : Contract := original1426.toContract.get (by decide)
theorem binding1426 : original1426.toContract = some c1426 := rfl

theorem checked1426 : check 4000 c1426 = true := by decide

def original1427 : RawOriginal := C011.records[19]'(by decide)
theorem original_id1427 : original1427.index = 1427 := by decide

def c1427 : Contract := original1427.toContract.get (by decide)
theorem binding1427 : original1427.toContract = some c1427 := rfl

theorem checked1427 : check 4000 c1427 = true := by decide

def original1428 : RawOriginal := C011.records[20]'(by decide)
theorem original_id1428 : original1428.index = 1428 := by decide

def c1428 : Contract := original1428.toContract.get (by decide)
theorem binding1428 : original1428.toContract = some c1428 := rfl

theorem checked1428 : check 4000 c1428 = true := by decide

def original1429 : RawOriginal := C011.records[21]'(by decide)
theorem original_id1429 : original1429.index = 1429 := by decide

def c1429 : Contract := original1429.toContract.get (by decide)
theorem binding1429 : original1429.toContract = some c1429 := rfl

theorem checked1429 : check 4000 c1429 = true := by decide

def records : List Certified := [
  ⟨1414, c1414, 4000, checked1414⟩,
  ⟨1415, c1415, 4000, checked1415⟩,
  ⟨1416, c1416, 4000, checked1416⟩,
  ⟨1417, c1417, 4000, checked1417⟩,
  ⟨1418, c1418, 4000, checked1418⟩,
  ⟨1419, c1419, 4000, checked1419⟩,
  ⟨1420, c1420, 4000, checked1420⟩,
  ⟨1421, c1421, 4000, checked1421⟩,
  ⟨1422, c1422, 4000, checked1422⟩,
  ⟨1423, c1423, 4000, checked1423⟩,
  ⟨1424, c1424, 4000, checked1424⟩,
  ⟨1425, c1425, 4000, checked1425⟩,
  ⟨1426, c1426, 4000, checked1426⟩,
  ⟨1427, c1427, 4000, checked1427⟩,
  ⟨1428, c1428, 4000, checked1428⟩,
  ⟨1429, c1429, 4000, checked1429⟩]

end PA215.ContractShards.Shard011Part0
