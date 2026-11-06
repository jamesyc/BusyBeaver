import PA215.CertifiedContracts
import PA215.Census.C011
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard011Part3
open PA215.Contracts PA215.Census

def original1462 : RawOriginal := C011.records[54]'(by decide)
theorem original_id1462 : original1462.index = 1462 := by decide

def c1462 : Contract := original1462.toContract.get (by decide)
theorem binding1462 : original1462.toContract = some c1462 := rfl

theorem checked1462 : check 4000 c1462 = true := by decide

def original1463 : RawOriginal := C011.records[55]'(by decide)
theorem original_id1463 : original1463.index = 1463 := by decide

def c1463 : Contract := original1463.toContract.get (by decide)
theorem binding1463 : original1463.toContract = some c1463 := rfl

theorem checked1463 : check 4000 c1463 = true := by decide

def original1464 : RawOriginal := C011.records[56]'(by decide)
theorem original_id1464 : original1464.index = 1464 := by decide

def c1464 : Contract := original1464.toContract.get (by decide)
theorem binding1464 : original1464.toContract = some c1464 := rfl

theorem checked1464 : check 4000 c1464 = true := by decide

def original1465 : RawOriginal := C011.records[57]'(by decide)
theorem original_id1465 : original1465.index = 1465 := by decide

def c1465 : Contract := original1465.toContract.get (by decide)
theorem binding1465 : original1465.toContract = some c1465 := rfl

theorem checked1465 : check 4000 c1465 = true := by decide

def original1466 : RawOriginal := C011.records[58]'(by decide)
theorem original_id1466 : original1466.index = 1466 := by decide

def c1466 : Contract := original1466.toContract.get (by decide)
theorem binding1466 : original1466.toContract = some c1466 := rfl

theorem checked1466 : check 4000 c1466 = true := by decide

def original1467 : RawOriginal := C011.records[59]'(by decide)
theorem original_id1467 : original1467.index = 1467 := by decide

def c1467 : Contract := original1467.toContract.get (by decide)
theorem binding1467 : original1467.toContract = some c1467 := rfl

theorem checked1467 : check 4000 c1467 = true := by decide

def original1468 : RawOriginal := C011.records[60]'(by decide)
theorem original_id1468 : original1468.index = 1468 := by decide

def c1468 : Contract := original1468.toContract.get (by decide)
theorem binding1468 : original1468.toContract = some c1468 := rfl

theorem checked1468 : check 4000 c1468 = true := by decide

def original1469 : RawOriginal := C011.records[61]'(by decide)
theorem original_id1469 : original1469.index = 1469 := by decide

def c1469 : Contract := original1469.toContract.get (by decide)
theorem binding1469 : original1469.toContract = some c1469 := rfl

theorem checked1469 : check 4000 c1469 = true := by decide

def original1470 : RawOriginal := C011.records[62]'(by decide)
theorem original_id1470 : original1470.index = 1470 := by decide

def c1470 : Contract := original1470.toContract.get (by decide)
theorem binding1470 : original1470.toContract = some c1470 := rfl

theorem checked1470 : check 4000 c1470 = true := by decide

def original1471 : RawOriginal := C011.records[63]'(by decide)
theorem original_id1471 : original1471.index = 1471 := by decide

def c1471 : Contract := original1471.toContract.get (by decide)
theorem binding1471 : original1471.toContract = some c1471 := rfl

theorem checked1471 : check 4000 c1471 = true := by decide

def original1472 : RawOriginal := C011.records[64]'(by decide)
theorem original_id1472 : original1472.index = 1472 := by decide

def c1472 : Contract := original1472.toContract.get (by decide)
theorem binding1472 : original1472.toContract = some c1472 := rfl

theorem checked1472 : check 4000 c1472 = true := by decide

def original1473 : RawOriginal := C011.records[65]'(by decide)
theorem original_id1473 : original1473.index = 1473 := by decide

def c1473 : Contract := original1473.toContract.get (by decide)
theorem binding1473 : original1473.toContract = some c1473 := rfl

theorem checked1473 : check 4000 c1473 = true := by decide

def original1474 : RawOriginal := C011.records[66]'(by decide)
theorem original_id1474 : original1474.index = 1474 := by decide

def c1474 : Contract := original1474.toContract.get (by decide)
theorem binding1474 : original1474.toContract = some c1474 := rfl

theorem checked1474 : check 4000 c1474 = true := by decide

def original1475 : RawOriginal := C011.records[67]'(by decide)
theorem original_id1475 : original1475.index = 1475 := by decide

def c1475 : Contract := original1475.toContract.get (by decide)
theorem binding1475 : original1475.toContract = some c1475 := rfl

theorem checked1475 : check 4000 c1475 = true := by decide

def original1476 : RawOriginal := C011.records[68]'(by decide)
theorem original_id1476 : original1476.index = 1476 := by decide

def c1476 : Contract := original1476.toContract.get (by decide)
theorem binding1476 : original1476.toContract = some c1476 := rfl

theorem checked1476 : check 4000 c1476 = true := by decide

def original1477 : RawOriginal := C011.records[69]'(by decide)
theorem original_id1477 : original1477.index = 1477 := by decide

def c1477 : Contract := original1477.toContract.get (by decide)
theorem binding1477 : original1477.toContract = some c1477 := rfl

theorem checked1477 : check 4000 c1477 = true := by decide

def records : List Certified := [
  ⟨1462, c1462, 4000, checked1462⟩,
  ⟨1463, c1463, 4000, checked1463⟩,
  ⟨1464, c1464, 4000, checked1464⟩,
  ⟨1465, c1465, 4000, checked1465⟩,
  ⟨1466, c1466, 4000, checked1466⟩,
  ⟨1467, c1467, 4000, checked1467⟩,
  ⟨1468, c1468, 4000, checked1468⟩,
  ⟨1469, c1469, 4000, checked1469⟩,
  ⟨1470, c1470, 4000, checked1470⟩,
  ⟨1471, c1471, 4000, checked1471⟩,
  ⟨1472, c1472, 4000, checked1472⟩,
  ⟨1473, c1473, 4000, checked1473⟩,
  ⟨1474, c1474, 4000, checked1474⟩,
  ⟨1475, c1475, 4000, checked1475⟩,
  ⟨1476, c1476, 4000, checked1476⟩,
  ⟨1477, c1477, 4000, checked1477⟩]

end PA215.ContractShards.Shard011Part3
