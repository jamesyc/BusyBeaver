import PA215.CertifiedContracts
import PA215.Census.C012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard012Part0
open PA215.Contracts PA215.Census

def original1542 : RawOriginal := C012.records[6]'(by decide)
theorem original_id1542 : original1542.index = 1542 := by decide

def c1542 : Contract := original1542.toContract.get (by decide)
theorem binding1542 : original1542.toContract = some c1542 := rfl

theorem checked1542 : check 4000 c1542 = true := by decide

def original1543 : RawOriginal := C012.records[7]'(by decide)
theorem original_id1543 : original1543.index = 1543 := by decide

def c1543 : Contract := original1543.toContract.get (by decide)
theorem binding1543 : original1543.toContract = some c1543 := rfl

theorem checked1543 : check 4000 c1543 = true := by decide

def original1544 : RawOriginal := C012.records[8]'(by decide)
theorem original_id1544 : original1544.index = 1544 := by decide

def c1544 : Contract := original1544.toContract.get (by decide)
theorem binding1544 : original1544.toContract = some c1544 := rfl

theorem checked1544 : check 4000 c1544 = true := by decide

def original1545 : RawOriginal := C012.records[9]'(by decide)
theorem original_id1545 : original1545.index = 1545 := by decide

def c1545 : Contract := original1545.toContract.get (by decide)
theorem binding1545 : original1545.toContract = some c1545 := rfl

theorem checked1545 : check 4000 c1545 = true := by decide

def original1546 : RawOriginal := C012.records[10]'(by decide)
theorem original_id1546 : original1546.index = 1546 := by decide

def c1546 : Contract := original1546.toContract.get (by decide)
theorem binding1546 : original1546.toContract = some c1546 := rfl

theorem checked1546 : check 4000 c1546 = true := by decide

def original1547 : RawOriginal := C012.records[11]'(by decide)
theorem original_id1547 : original1547.index = 1547 := by decide

def c1547 : Contract := original1547.toContract.get (by decide)
theorem binding1547 : original1547.toContract = some c1547 := rfl

theorem checked1547 : check 4000 c1547 = true := by decide

def original1548 : RawOriginal := C012.records[12]'(by decide)
theorem original_id1548 : original1548.index = 1548 := by decide

def c1548 : Contract := original1548.toContract.get (by decide)
theorem binding1548 : original1548.toContract = some c1548 := rfl

theorem checked1548 : check 4000 c1548 = true := by decide

def original1549 : RawOriginal := C012.records[13]'(by decide)
theorem original_id1549 : original1549.index = 1549 := by decide

def c1549 : Contract := original1549.toContract.get (by decide)
theorem binding1549 : original1549.toContract = some c1549 := rfl

theorem checked1549 : check 4000 c1549 = true := by decide

def original1550 : RawOriginal := C012.records[14]'(by decide)
theorem original_id1550 : original1550.index = 1550 := by decide

def c1550 : Contract := original1550.toContract.get (by decide)
theorem binding1550 : original1550.toContract = some c1550 := rfl

theorem checked1550 : check 4000 c1550 = true := by decide

def original1551 : RawOriginal := C012.records[15]'(by decide)
theorem original_id1551 : original1551.index = 1551 := by decide

def c1551 : Contract := original1551.toContract.get (by decide)
theorem binding1551 : original1551.toContract = some c1551 := rfl

theorem checked1551 : check 4000 c1551 = true := by decide

def original1552 : RawOriginal := C012.records[16]'(by decide)
theorem original_id1552 : original1552.index = 1552 := by decide

def c1552 : Contract := original1552.toContract.get (by decide)
theorem binding1552 : original1552.toContract = some c1552 := rfl

theorem checked1552 : check 4000 c1552 = true := by decide

def original1553 : RawOriginal := C012.records[17]'(by decide)
theorem original_id1553 : original1553.index = 1553 := by decide

def c1553 : Contract := original1553.toContract.get (by decide)
theorem binding1553 : original1553.toContract = some c1553 := rfl

theorem checked1553 : check 4000 c1553 = true := by decide

def original1554 : RawOriginal := C012.records[18]'(by decide)
theorem original_id1554 : original1554.index = 1554 := by decide

def c1554 : Contract := original1554.toContract.get (by decide)
theorem binding1554 : original1554.toContract = some c1554 := rfl

theorem checked1554 : check 4000 c1554 = true := by decide

def original1555 : RawOriginal := C012.records[19]'(by decide)
theorem original_id1555 : original1555.index = 1555 := by decide

def c1555 : Contract := original1555.toContract.get (by decide)
theorem binding1555 : original1555.toContract = some c1555 := rfl

theorem checked1555 : check 4000 c1555 = true := by decide

def original1556 : RawOriginal := C012.records[20]'(by decide)
theorem original_id1556 : original1556.index = 1556 := by decide

def c1556 : Contract := original1556.toContract.get (by decide)
theorem binding1556 : original1556.toContract = some c1556 := rfl

theorem checked1556 : check 4000 c1556 = true := by decide

def original1557 : RawOriginal := C012.records[21]'(by decide)
theorem original_id1557 : original1557.index = 1557 := by decide

def c1557 : Contract := original1557.toContract.get (by decide)
theorem binding1557 : original1557.toContract = some c1557 := rfl

theorem checked1557 : check 4000 c1557 = true := by decide

def records : List Certified := [
  ⟨1542, c1542, 4000, checked1542⟩,
  ⟨1543, c1543, 4000, checked1543⟩,
  ⟨1544, c1544, 4000, checked1544⟩,
  ⟨1545, c1545, 4000, checked1545⟩,
  ⟨1546, c1546, 4000, checked1546⟩,
  ⟨1547, c1547, 4000, checked1547⟩,
  ⟨1548, c1548, 4000, checked1548⟩,
  ⟨1549, c1549, 4000, checked1549⟩,
  ⟨1550, c1550, 4000, checked1550⟩,
  ⟨1551, c1551, 4000, checked1551⟩,
  ⟨1552, c1552, 4000, checked1552⟩,
  ⟨1553, c1553, 4000, checked1553⟩,
  ⟨1554, c1554, 4000, checked1554⟩,
  ⟨1555, c1555, 4000, checked1555⟩,
  ⟨1556, c1556, 4000, checked1556⟩,
  ⟨1557, c1557, 4000, checked1557⟩]

end PA215.ContractShards.Shard012Part0
