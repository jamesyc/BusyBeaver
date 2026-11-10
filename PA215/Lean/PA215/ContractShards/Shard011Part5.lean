import PA215.CertifiedContracts
import PA215.Census.C011
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard011Part5
open PA215.Contracts PA215.Census

def original1494 : RawOriginal := C011.records[86]'(by decide)
theorem original_id1494 : original1494.index = 1494 := by decide

def c1494 : Contract := original1494.toContract.get (by decide)
theorem binding1494 : original1494.toContract = some c1494 := rfl

theorem checked1494 : check 4000 c1494 = true := by decide

def original1495 : RawOriginal := C011.records[87]'(by decide)
theorem original_id1495 : original1495.index = 1495 := by decide

def c1495 : Contract := original1495.toContract.get (by decide)
theorem binding1495 : original1495.toContract = some c1495 := rfl

theorem checked1495 : check 4000 c1495 = true := by decide

def original1496 : RawOriginal := C011.records[88]'(by decide)
theorem original_id1496 : original1496.index = 1496 := by decide

def c1496 : Contract := original1496.toContract.get (by decide)
theorem binding1496 : original1496.toContract = some c1496 := rfl

theorem checked1496 : check 4000 c1496 = true := by decide

def original1497 : RawOriginal := C011.records[89]'(by decide)
theorem original_id1497 : original1497.index = 1497 := by decide

def c1497 : Contract := original1497.toContract.get (by decide)
theorem binding1497 : original1497.toContract = some c1497 := rfl

theorem checked1497 : check 4000 c1497 = true := by decide

def original1498 : RawOriginal := C011.records[90]'(by decide)
theorem original_id1498 : original1498.index = 1498 := by decide

def c1498 : Contract := original1498.toContract.get (by decide)
theorem binding1498 : original1498.toContract = some c1498 := rfl

theorem checked1498 : check 4000 c1498 = true := by decide

def original1499 : RawOriginal := C011.records[91]'(by decide)
theorem original_id1499 : original1499.index = 1499 := by decide

def c1499 : Contract := original1499.toContract.get (by decide)
theorem binding1499 : original1499.toContract = some c1499 := rfl

theorem checked1499 : check 4000 c1499 = true := by decide

def original1500 : RawOriginal := C011.records[92]'(by decide)
theorem original_id1500 : original1500.index = 1500 := by decide

def c1500 : Contract := original1500.toContract.get (by decide)
theorem binding1500 : original1500.toContract = some c1500 := rfl

theorem checked1500 : check 4000 c1500 = true := by decide

def original1501 : RawOriginal := C011.records[93]'(by decide)
theorem original_id1501 : original1501.index = 1501 := by decide

def c1501 : Contract := original1501.toContract.get (by decide)
theorem binding1501 : original1501.toContract = some c1501 := rfl

theorem checked1501 : check 4000 c1501 = true := by decide

def original1502 : RawOriginal := C011.records[94]'(by decide)
theorem original_id1502 : original1502.index = 1502 := by decide

def c1502 : Contract := original1502.toContract.get (by decide)
theorem binding1502 : original1502.toContract = some c1502 := rfl

theorem checked1502 : check 4000 c1502 = true := by decide

def original1503 : RawOriginal := C011.records[95]'(by decide)
theorem original_id1503 : original1503.index = 1503 := by decide

def c1503 : Contract := original1503.toContract.get (by decide)
theorem binding1503 : original1503.toContract = some c1503 := rfl

theorem checked1503 : check 4000 c1503 = true := by decide

def original1504 : RawOriginal := C011.records[96]'(by decide)
theorem original_id1504 : original1504.index = 1504 := by decide

def c1504 : Contract := original1504.toContract.get (by decide)
theorem binding1504 : original1504.toContract = some c1504 := rfl

theorem checked1504 : check 4000 c1504 = true := by decide

def original1505 : RawOriginal := C011.records[97]'(by decide)
theorem original_id1505 : original1505.index = 1505 := by decide

def c1505 : Contract := original1505.toContract.get (by decide)
theorem binding1505 : original1505.toContract = some c1505 := rfl

theorem checked1505 : check 4000 c1505 = true := by decide

def original1506 : RawOriginal := C011.records[98]'(by decide)
theorem original_id1506 : original1506.index = 1506 := by decide

def c1506 : Contract := original1506.toContract.get (by decide)
theorem binding1506 : original1506.toContract = some c1506 := rfl

theorem checked1506 : check 4000 c1506 = true := by decide

def original1507 : RawOriginal := C011.records[99]'(by decide)
theorem original_id1507 : original1507.index = 1507 := by decide

def c1507 : Contract := original1507.toContract.get (by decide)
theorem binding1507 : original1507.toContract = some c1507 := rfl

theorem checked1507 : check 4000 c1507 = true := by decide

def original1508 : RawOriginal := C011.records[100]'(by decide)
theorem original_id1508 : original1508.index = 1508 := by decide

def c1508 : Contract := original1508.toContract.get (by decide)
theorem binding1508 : original1508.toContract = some c1508 := rfl

theorem checked1508 : check 4000 c1508 = true := by decide

def original1509 : RawOriginal := C011.records[101]'(by decide)
theorem original_id1509 : original1509.index = 1509 := by decide

def c1509 : Contract := original1509.toContract.get (by decide)
theorem binding1509 : original1509.toContract = some c1509 := rfl

theorem checked1509 : check 4000 c1509 = true := by decide

def records : List Certified := [
  ⟨1494, c1494, 4000, checked1494⟩,
  ⟨1495, c1495, 4000, checked1495⟩,
  ⟨1496, c1496, 4000, checked1496⟩,
  ⟨1497, c1497, 4000, checked1497⟩,
  ⟨1498, c1498, 4000, checked1498⟩,
  ⟨1499, c1499, 4000, checked1499⟩,
  ⟨1500, c1500, 4000, checked1500⟩,
  ⟨1501, c1501, 4000, checked1501⟩,
  ⟨1502, c1502, 4000, checked1502⟩,
  ⟨1503, c1503, 4000, checked1503⟩,
  ⟨1504, c1504, 4000, checked1504⟩,
  ⟨1505, c1505, 4000, checked1505⟩,
  ⟨1506, c1506, 4000, checked1506⟩,
  ⟨1507, c1507, 4000, checked1507⟩,
  ⟨1508, c1508, 4000, checked1508⟩,
  ⟨1509, c1509, 4000, checked1509⟩]

end PA215.ContractShards.Shard011Part5
