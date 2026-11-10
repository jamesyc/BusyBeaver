import PA215.CertifiedContracts
import PA215.Census.C011
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard011Part4
open PA215.Contracts PA215.Census

def original1478 : RawOriginal := C011.records[70]'(by decide)
theorem original_id1478 : original1478.index = 1478 := by decide

def c1478 : Contract := original1478.toContract.get (by decide)
theorem binding1478 : original1478.toContract = some c1478 := rfl

theorem checked1478 : check 4000 c1478 = true := by decide

def original1479 : RawOriginal := C011.records[71]'(by decide)
theorem original_id1479 : original1479.index = 1479 := by decide

def c1479 : Contract := original1479.toContract.get (by decide)
theorem binding1479 : original1479.toContract = some c1479 := rfl

theorem checked1479 : check 4000 c1479 = true := by decide

def original1480 : RawOriginal := C011.records[72]'(by decide)
theorem original_id1480 : original1480.index = 1480 := by decide

def c1480 : Contract := original1480.toContract.get (by decide)
theorem binding1480 : original1480.toContract = some c1480 := rfl

theorem checked1480 : check 4000 c1480 = true := by decide

def original1481 : RawOriginal := C011.records[73]'(by decide)
theorem original_id1481 : original1481.index = 1481 := by decide

def c1481 : Contract := original1481.toContract.get (by decide)
theorem binding1481 : original1481.toContract = some c1481 := rfl

theorem checked1481 : check 4000 c1481 = true := by decide

def original1482 : RawOriginal := C011.records[74]'(by decide)
theorem original_id1482 : original1482.index = 1482 := by decide

def c1482 : Contract := original1482.toContract.get (by decide)
theorem binding1482 : original1482.toContract = some c1482 := rfl

theorem checked1482 : check 4000 c1482 = true := by decide

def original1483 : RawOriginal := C011.records[75]'(by decide)
theorem original_id1483 : original1483.index = 1483 := by decide

def c1483 : Contract := original1483.toContract.get (by decide)
theorem binding1483 : original1483.toContract = some c1483 := rfl

theorem checked1483 : check 4000 c1483 = true := by decide

def original1484 : RawOriginal := C011.records[76]'(by decide)
theorem original_id1484 : original1484.index = 1484 := by decide

def c1484 : Contract := original1484.toContract.get (by decide)
theorem binding1484 : original1484.toContract = some c1484 := rfl

theorem checked1484 : check 4000 c1484 = true := by decide

def original1485 : RawOriginal := C011.records[77]'(by decide)
theorem original_id1485 : original1485.index = 1485 := by decide

def c1485 : Contract := original1485.toContract.get (by decide)
theorem binding1485 : original1485.toContract = some c1485 := rfl

theorem checked1485 : check 4000 c1485 = true := by decide

def original1486 : RawOriginal := C011.records[78]'(by decide)
theorem original_id1486 : original1486.index = 1486 := by decide

def c1486 : Contract := original1486.toContract.get (by decide)
theorem binding1486 : original1486.toContract = some c1486 := rfl

theorem checked1486 : check 4000 c1486 = true := by decide

def original1487 : RawOriginal := C011.records[79]'(by decide)
theorem original_id1487 : original1487.index = 1487 := by decide

def c1487 : Contract := original1487.toContract.get (by decide)
theorem binding1487 : original1487.toContract = some c1487 := rfl

theorem checked1487 : check 4000 c1487 = true := by decide

def original1488 : RawOriginal := C011.records[80]'(by decide)
theorem original_id1488 : original1488.index = 1488 := by decide

def c1488 : Contract := original1488.toContract.get (by decide)
theorem binding1488 : original1488.toContract = some c1488 := rfl

theorem checked1488 : check 4000 c1488 = true := by decide

def original1489 : RawOriginal := C011.records[81]'(by decide)
theorem original_id1489 : original1489.index = 1489 := by decide

def c1489 : Contract := original1489.toContract.get (by decide)
theorem binding1489 : original1489.toContract = some c1489 := rfl

theorem checked1489 : check 4000 c1489 = true := by decide

def original1490 : RawOriginal := C011.records[82]'(by decide)
theorem original_id1490 : original1490.index = 1490 := by decide

def c1490 : Contract := original1490.toContract.get (by decide)
theorem binding1490 : original1490.toContract = some c1490 := rfl

theorem checked1490 : check 4000 c1490 = true := by decide

def original1491 : RawOriginal := C011.records[83]'(by decide)
theorem original_id1491 : original1491.index = 1491 := by decide

def c1491 : Contract := original1491.toContract.get (by decide)
theorem binding1491 : original1491.toContract = some c1491 := rfl

theorem checked1491 : check 4000 c1491 = true := by decide

def original1492 : RawOriginal := C011.records[84]'(by decide)
theorem original_id1492 : original1492.index = 1492 := by decide

def c1492 : Contract := original1492.toContract.get (by decide)
theorem binding1492 : original1492.toContract = some c1492 := rfl

theorem checked1492 : check 4000 c1492 = true := by decide

def original1493 : RawOriginal := C011.records[85]'(by decide)
theorem original_id1493 : original1493.index = 1493 := by decide

def c1493 : Contract := original1493.toContract.get (by decide)
theorem binding1493 : original1493.toContract = some c1493 := rfl

theorem checked1493 : check 4000 c1493 = true := by decide

def records : List Certified := [
  ⟨1478, c1478, 4000, checked1478⟩,
  ⟨1479, c1479, 4000, checked1479⟩,
  ⟨1480, c1480, 4000, checked1480⟩,
  ⟨1481, c1481, 4000, checked1481⟩,
  ⟨1482, c1482, 4000, checked1482⟩,
  ⟨1483, c1483, 4000, checked1483⟩,
  ⟨1484, c1484, 4000, checked1484⟩,
  ⟨1485, c1485, 4000, checked1485⟩,
  ⟨1486, c1486, 4000, checked1486⟩,
  ⟨1487, c1487, 4000, checked1487⟩,
  ⟨1488, c1488, 4000, checked1488⟩,
  ⟨1489, c1489, 4000, checked1489⟩,
  ⟨1490, c1490, 4000, checked1490⟩,
  ⟨1491, c1491, 4000, checked1491⟩,
  ⟨1492, c1492, 4000, checked1492⟩,
  ⟨1493, c1493, 4000, checked1493⟩]

end PA215.ContractShards.Shard011Part4
