import PA215.CertifiedContracts
import PA215.Census.C011
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard011Part1
open PA215.Contracts PA215.Census

def original1430 : RawOriginal := C011.records[22]'(by decide)
theorem original_id1430 : original1430.index = 1430 := by decide

def c1430 : Contract := original1430.toContract.get (by decide)
theorem binding1430 : original1430.toContract = some c1430 := rfl

theorem checked1430 : check 4000 c1430 = true := by decide

def original1431 : RawOriginal := C011.records[23]'(by decide)
theorem original_id1431 : original1431.index = 1431 := by decide

def c1431 : Contract := original1431.toContract.get (by decide)
theorem binding1431 : original1431.toContract = some c1431 := rfl

theorem checked1431 : check 4000 c1431 = true := by decide

def original1432 : RawOriginal := C011.records[24]'(by decide)
theorem original_id1432 : original1432.index = 1432 := by decide

def c1432 : Contract := original1432.toContract.get (by decide)
theorem binding1432 : original1432.toContract = some c1432 := rfl

theorem checked1432 : check 4000 c1432 = true := by decide

def original1433 : RawOriginal := C011.records[25]'(by decide)
theorem original_id1433 : original1433.index = 1433 := by decide

def c1433 : Contract := original1433.toContract.get (by decide)
theorem binding1433 : original1433.toContract = some c1433 := rfl

theorem checked1433 : check 4000 c1433 = true := by decide

def original1434 : RawOriginal := C011.records[26]'(by decide)
theorem original_id1434 : original1434.index = 1434 := by decide

def c1434 : Contract := original1434.toContract.get (by decide)
theorem binding1434 : original1434.toContract = some c1434 := rfl

theorem checked1434 : check 4000 c1434 = true := by decide

def original1435 : RawOriginal := C011.records[27]'(by decide)
theorem original_id1435 : original1435.index = 1435 := by decide

def c1435 : Contract := original1435.toContract.get (by decide)
theorem binding1435 : original1435.toContract = some c1435 := rfl

theorem checked1435 : check 4000 c1435 = true := by decide

def original1436 : RawOriginal := C011.records[28]'(by decide)
theorem original_id1436 : original1436.index = 1436 := by decide

def c1436 : Contract := original1436.toContract.get (by decide)
theorem binding1436 : original1436.toContract = some c1436 := rfl

theorem checked1436 : check 4000 c1436 = true := by decide

def original1437 : RawOriginal := C011.records[29]'(by decide)
theorem original_id1437 : original1437.index = 1437 := by decide

def c1437 : Contract := original1437.toContract.get (by decide)
theorem binding1437 : original1437.toContract = some c1437 := rfl

theorem checked1437 : check 4000 c1437 = true := by decide

def original1438 : RawOriginal := C011.records[30]'(by decide)
theorem original_id1438 : original1438.index = 1438 := by decide

def c1438 : Contract := original1438.toContract.get (by decide)
theorem binding1438 : original1438.toContract = some c1438 := rfl

theorem checked1438 : check 4000 c1438 = true := by decide

def original1439 : RawOriginal := C011.records[31]'(by decide)
theorem original_id1439 : original1439.index = 1439 := by decide

def c1439 : Contract := original1439.toContract.get (by decide)
theorem binding1439 : original1439.toContract = some c1439 := rfl

theorem checked1439 : check 4000 c1439 = true := by decide

def original1440 : RawOriginal := C011.records[32]'(by decide)
theorem original_id1440 : original1440.index = 1440 := by decide

def c1440 : Contract := original1440.toContract.get (by decide)
theorem binding1440 : original1440.toContract = some c1440 := rfl

theorem checked1440 : check 4000 c1440 = true := by decide

def original1441 : RawOriginal := C011.records[33]'(by decide)
theorem original_id1441 : original1441.index = 1441 := by decide

def c1441 : Contract := original1441.toContract.get (by decide)
theorem binding1441 : original1441.toContract = some c1441 := rfl

theorem checked1441 : check 4000 c1441 = true := by decide

def original1442 : RawOriginal := C011.records[34]'(by decide)
theorem original_id1442 : original1442.index = 1442 := by decide

def c1442 : Contract := original1442.toContract.get (by decide)
theorem binding1442 : original1442.toContract = some c1442 := rfl

theorem checked1442 : check 4000 c1442 = true := by decide

def original1443 : RawOriginal := C011.records[35]'(by decide)
theorem original_id1443 : original1443.index = 1443 := by decide

def c1443 : Contract := original1443.toContract.get (by decide)
theorem binding1443 : original1443.toContract = some c1443 := rfl

theorem checked1443 : check 4000 c1443 = true := by decide

def original1444 : RawOriginal := C011.records[36]'(by decide)
theorem original_id1444 : original1444.index = 1444 := by decide

def c1444 : Contract := original1444.toContract.get (by decide)
theorem binding1444 : original1444.toContract = some c1444 := rfl

theorem checked1444 : check 4000 c1444 = true := by decide

def original1445 : RawOriginal := C011.records[37]'(by decide)
theorem original_id1445 : original1445.index = 1445 := by decide

def c1445 : Contract := original1445.toContract.get (by decide)
theorem binding1445 : original1445.toContract = some c1445 := rfl

theorem checked1445 : check 4000 c1445 = true := by decide

def records : List Certified := [
  ⟨1430, c1430, 4000, checked1430⟩,
  ⟨1431, c1431, 4000, checked1431⟩,
  ⟨1432, c1432, 4000, checked1432⟩,
  ⟨1433, c1433, 4000, checked1433⟩,
  ⟨1434, c1434, 4000, checked1434⟩,
  ⟨1435, c1435, 4000, checked1435⟩,
  ⟨1436, c1436, 4000, checked1436⟩,
  ⟨1437, c1437, 4000, checked1437⟩,
  ⟨1438, c1438, 4000, checked1438⟩,
  ⟨1439, c1439, 4000, checked1439⟩,
  ⟨1440, c1440, 4000, checked1440⟩,
  ⟨1441, c1441, 4000, checked1441⟩,
  ⟨1442, c1442, 4000, checked1442⟩,
  ⟨1443, c1443, 4000, checked1443⟩,
  ⟨1444, c1444, 4000, checked1444⟩,
  ⟨1445, c1445, 4000, checked1445⟩]

end PA215.ContractShards.Shard011Part1
