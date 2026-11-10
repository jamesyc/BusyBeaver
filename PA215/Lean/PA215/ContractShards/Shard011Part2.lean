import PA215.CertifiedContracts
import PA215.Census.C011
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard011Part2
open PA215.Contracts PA215.Census

def original1446 : RawOriginal := C011.records[38]'(by decide)
theorem original_id1446 : original1446.index = 1446 := by decide

def c1446 : Contract := original1446.toContract.get (by decide)
theorem binding1446 : original1446.toContract = some c1446 := rfl

theorem checked1446 : check 4000 c1446 = true := by decide

def original1447 : RawOriginal := C011.records[39]'(by decide)
theorem original_id1447 : original1447.index = 1447 := by decide

def c1447 : Contract := original1447.toContract.get (by decide)
theorem binding1447 : original1447.toContract = some c1447 := rfl

theorem checked1447 : check 4000 c1447 = true := by decide

def original1448 : RawOriginal := C011.records[40]'(by decide)
theorem original_id1448 : original1448.index = 1448 := by decide

def c1448 : Contract := original1448.toContract.get (by decide)
theorem binding1448 : original1448.toContract = some c1448 := rfl

theorem checked1448 : check 4000 c1448 = true := by decide

def original1449 : RawOriginal := C011.records[41]'(by decide)
theorem original_id1449 : original1449.index = 1449 := by decide

def c1449 : Contract := original1449.toContract.get (by decide)
theorem binding1449 : original1449.toContract = some c1449 := rfl

theorem checked1449 : check 4000 c1449 = true := by decide

def original1450 : RawOriginal := C011.records[42]'(by decide)
theorem original_id1450 : original1450.index = 1450 := by decide

def c1450 : Contract := original1450.toContract.get (by decide)
theorem binding1450 : original1450.toContract = some c1450 := rfl

theorem checked1450 : check 4000 c1450 = true := by decide

def original1451 : RawOriginal := C011.records[43]'(by decide)
theorem original_id1451 : original1451.index = 1451 := by decide

def c1451 : Contract := original1451.toContract.get (by decide)
theorem binding1451 : original1451.toContract = some c1451 := rfl

theorem checked1451 : check 4000 c1451 = true := by decide

def original1452 : RawOriginal := C011.records[44]'(by decide)
theorem original_id1452 : original1452.index = 1452 := by decide

def c1452 : Contract := original1452.toContract.get (by decide)
theorem binding1452 : original1452.toContract = some c1452 := rfl

theorem checked1452 : check 4000 c1452 = true := by decide

def original1453 : RawOriginal := C011.records[45]'(by decide)
theorem original_id1453 : original1453.index = 1453 := by decide

def c1453 : Contract := original1453.toContract.get (by decide)
theorem binding1453 : original1453.toContract = some c1453 := rfl

theorem checked1453 : check 4000 c1453 = true := by decide

def original1454 : RawOriginal := C011.records[46]'(by decide)
theorem original_id1454 : original1454.index = 1454 := by decide

def c1454 : Contract := original1454.toContract.get (by decide)
theorem binding1454 : original1454.toContract = some c1454 := rfl

theorem checked1454 : check 4000 c1454 = true := by decide

def original1455 : RawOriginal := C011.records[47]'(by decide)
theorem original_id1455 : original1455.index = 1455 := by decide

def c1455 : Contract := original1455.toContract.get (by decide)
theorem binding1455 : original1455.toContract = some c1455 := rfl

theorem checked1455 : check 4000 c1455 = true := by decide

def original1456 : RawOriginal := C011.records[48]'(by decide)
theorem original_id1456 : original1456.index = 1456 := by decide

def c1456 : Contract := original1456.toContract.get (by decide)
theorem binding1456 : original1456.toContract = some c1456 := rfl

theorem checked1456 : check 4000 c1456 = true := by decide

def original1457 : RawOriginal := C011.records[49]'(by decide)
theorem original_id1457 : original1457.index = 1457 := by decide

def c1457 : Contract := original1457.toContract.get (by decide)
theorem binding1457 : original1457.toContract = some c1457 := rfl

theorem checked1457 : check 4000 c1457 = true := by decide

def original1458 : RawOriginal := C011.records[50]'(by decide)
theorem original_id1458 : original1458.index = 1458 := by decide

def c1458 : Contract := original1458.toContract.get (by decide)
theorem binding1458 : original1458.toContract = some c1458 := rfl

theorem checked1458 : check 4000 c1458 = true := by decide

def original1459 : RawOriginal := C011.records[51]'(by decide)
theorem original_id1459 : original1459.index = 1459 := by decide

def c1459 : Contract := original1459.toContract.get (by decide)
theorem binding1459 : original1459.toContract = some c1459 := rfl

theorem checked1459 : check 4000 c1459 = true := by decide

def original1460 : RawOriginal := C011.records[52]'(by decide)
theorem original_id1460 : original1460.index = 1460 := by decide

def c1460 : Contract := original1460.toContract.get (by decide)
theorem binding1460 : original1460.toContract = some c1460 := rfl

theorem checked1460 : check 4000 c1460 = true := by decide

def original1461 : RawOriginal := C011.records[53]'(by decide)
theorem original_id1461 : original1461.index = 1461 := by decide

def c1461 : Contract := original1461.toContract.get (by decide)
theorem binding1461 : original1461.toContract = some c1461 := rfl

theorem checked1461 : check 4000 c1461 = true := by decide

def records : List Certified := [
  ⟨1446, c1446, 4000, checked1446⟩,
  ⟨1447, c1447, 4000, checked1447⟩,
  ⟨1448, c1448, 4000, checked1448⟩,
  ⟨1449, c1449, 4000, checked1449⟩,
  ⟨1450, c1450, 4000, checked1450⟩,
  ⟨1451, c1451, 4000, checked1451⟩,
  ⟨1452, c1452, 4000, checked1452⟩,
  ⟨1453, c1453, 4000, checked1453⟩,
  ⟨1454, c1454, 4000, checked1454⟩,
  ⟨1455, c1455, 4000, checked1455⟩,
  ⟨1456, c1456, 4000, checked1456⟩,
  ⟨1457, c1457, 4000, checked1457⟩,
  ⟨1458, c1458, 4000, checked1458⟩,
  ⟨1459, c1459, 4000, checked1459⟩,
  ⟨1460, c1460, 4000, checked1460⟩,
  ⟨1461, c1461, 4000, checked1461⟩]

end PA215.ContractShards.Shard011Part2
