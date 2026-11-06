import PA215.CertifiedContracts
import PA215.Census.C011
import PA215.Census.C012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard011Part7
open PA215.Contracts PA215.Census

def original1526 : RawOriginal := C011.records[118]'(by decide)
theorem original_id1526 : original1526.index = 1526 := by decide

def c1526 : Contract := original1526.toContract.get (by decide)
theorem binding1526 : original1526.toContract = some c1526 := rfl

theorem checked1526 : check 4000 c1526 = true := by decide

def original1527 : RawOriginal := C011.records[119]'(by decide)
theorem original_id1527 : original1527.index = 1527 := by decide

def c1527 : Contract := original1527.toContract.get (by decide)
theorem binding1527 : original1527.toContract = some c1527 := rfl

theorem checked1527 : check 4000 c1527 = true := by decide

def original1528 : RawOriginal := C011.records[120]'(by decide)
theorem original_id1528 : original1528.index = 1528 := by decide

def c1528 : Contract := original1528.toContract.get (by decide)
theorem binding1528 : original1528.toContract = some c1528 := rfl

theorem checked1528 : check 4000 c1528 = true := by decide

def original1529 : RawOriginal := C011.records[121]'(by decide)
theorem original_id1529 : original1529.index = 1529 := by decide

def c1529 : Contract := original1529.toContract.get (by decide)
theorem binding1529 : original1529.toContract = some c1529 := rfl

theorem checked1529 : check 4000 c1529 = true := by decide

def original1530 : RawOriginal := C011.records[122]'(by decide)
theorem original_id1530 : original1530.index = 1530 := by decide

def c1530 : Contract := original1530.toContract.get (by decide)
theorem binding1530 : original1530.toContract = some c1530 := rfl

theorem checked1530 : check 4000 c1530 = true := by decide

def original1531 : RawOriginal := C011.records[123]'(by decide)
theorem original_id1531 : original1531.index = 1531 := by decide

def c1531 : Contract := original1531.toContract.get (by decide)
theorem binding1531 : original1531.toContract = some c1531 := rfl

theorem checked1531 : check 4000 c1531 = true := by decide

def original1532 : RawOriginal := C011.records[124]'(by decide)
theorem original_id1532 : original1532.index = 1532 := by decide

def c1532 : Contract := original1532.toContract.get (by decide)
theorem binding1532 : original1532.toContract = some c1532 := rfl

theorem checked1532 : check 4000 c1532 = true := by decide

def original1533 : RawOriginal := C011.records[125]'(by decide)
theorem original_id1533 : original1533.index = 1533 := by decide

def c1533 : Contract := original1533.toContract.get (by decide)
theorem binding1533 : original1533.toContract = some c1533 := rfl

theorem checked1533 : check 4000 c1533 = true := by decide

def original1534 : RawOriginal := C011.records[126]'(by decide)
theorem original_id1534 : original1534.index = 1534 := by decide

def c1534 : Contract := original1534.toContract.get (by decide)
theorem binding1534 : original1534.toContract = some c1534 := rfl

theorem checked1534 : check 4000 c1534 = true := by decide

def original1535 : RawOriginal := C011.records[127]'(by decide)
theorem original_id1535 : original1535.index = 1535 := by decide

def c1535 : Contract := original1535.toContract.get (by decide)
theorem binding1535 : original1535.toContract = some c1535 := rfl

theorem checked1535 : check 4000 c1535 = true := by decide

def original1536 : RawOriginal := C012.records[0]'(by decide)
theorem original_id1536 : original1536.index = 1536 := by decide

def c1536 : Contract := original1536.toContract.get (by decide)
theorem binding1536 : original1536.toContract = some c1536 := rfl

theorem checked1536 : check 4000 c1536 = true := by decide

def original1537 : RawOriginal := C012.records[1]'(by decide)
theorem original_id1537 : original1537.index = 1537 := by decide

def c1537 : Contract := original1537.toContract.get (by decide)
theorem binding1537 : original1537.toContract = some c1537 := rfl

theorem checked1537 : check 4000 c1537 = true := by decide

def original1538 : RawOriginal := C012.records[2]'(by decide)
theorem original_id1538 : original1538.index = 1538 := by decide

def c1538 : Contract := original1538.toContract.get (by decide)
theorem binding1538 : original1538.toContract = some c1538 := rfl

theorem checked1538 : check 4000 c1538 = true := by decide

def original1539 : RawOriginal := C012.records[3]'(by decide)
theorem original_id1539 : original1539.index = 1539 := by decide

def c1539 : Contract := original1539.toContract.get (by decide)
theorem binding1539 : original1539.toContract = some c1539 := rfl

theorem checked1539 : check 4000 c1539 = true := by decide

def original1540 : RawOriginal := C012.records[4]'(by decide)
theorem original_id1540 : original1540.index = 1540 := by decide

def c1540 : Contract := original1540.toContract.get (by decide)
theorem binding1540 : original1540.toContract = some c1540 := rfl

theorem checked1540 : check 4000 c1540 = true := by decide

def original1541 : RawOriginal := C012.records[5]'(by decide)
theorem original_id1541 : original1541.index = 1541 := by decide

def c1541 : Contract := original1541.toContract.get (by decide)
theorem binding1541 : original1541.toContract = some c1541 := rfl

theorem checked1541 : check 4000 c1541 = true := by decide

def records : List Certified := [
  ⟨1526, c1526, 4000, checked1526⟩,
  ⟨1527, c1527, 4000, checked1527⟩,
  ⟨1528, c1528, 4000, checked1528⟩,
  ⟨1529, c1529, 4000, checked1529⟩,
  ⟨1530, c1530, 4000, checked1530⟩,
  ⟨1531, c1531, 4000, checked1531⟩,
  ⟨1532, c1532, 4000, checked1532⟩,
  ⟨1533, c1533, 4000, checked1533⟩,
  ⟨1534, c1534, 4000, checked1534⟩,
  ⟨1535, c1535, 4000, checked1535⟩,
  ⟨1536, c1536, 4000, checked1536⟩,
  ⟨1537, c1537, 4000, checked1537⟩,
  ⟨1538, c1538, 4000, checked1538⟩,
  ⟨1539, c1539, 4000, checked1539⟩,
  ⟨1540, c1540, 4000, checked1540⟩,
  ⟨1541, c1541, 4000, checked1541⟩]

end PA215.ContractShards.Shard011Part7
