import PA215.CertifiedContracts
import PA215.Census.C011
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard011Part6
open PA215.Contracts PA215.Census

def original1510 : RawOriginal := C011.records[102]'(by decide)
theorem original_id1510 : original1510.index = 1510 := by decide

def c1510 : Contract := original1510.toContract.get (by decide)
theorem binding1510 : original1510.toContract = some c1510 := rfl

theorem checked1510 : check 4000 c1510 = true := by decide

def original1511 : RawOriginal := C011.records[103]'(by decide)
theorem original_id1511 : original1511.index = 1511 := by decide

def c1511 : Contract := original1511.toContract.get (by decide)
theorem binding1511 : original1511.toContract = some c1511 := rfl

theorem checked1511 : check 4000 c1511 = true := by decide

def original1512 : RawOriginal := C011.records[104]'(by decide)
theorem original_id1512 : original1512.index = 1512 := by decide

def c1512 : Contract := original1512.toContract.get (by decide)
theorem binding1512 : original1512.toContract = some c1512 := rfl

theorem checked1512 : check 4000 c1512 = true := by decide

def original1513 : RawOriginal := C011.records[105]'(by decide)
theorem original_id1513 : original1513.index = 1513 := by decide

def c1513 : Contract := original1513.toContract.get (by decide)
theorem binding1513 : original1513.toContract = some c1513 := rfl

theorem checked1513 : check 4000 c1513 = true := by decide

def original1514 : RawOriginal := C011.records[106]'(by decide)
theorem original_id1514 : original1514.index = 1514 := by decide

def c1514 : Contract := original1514.toContract.get (by decide)
theorem binding1514 : original1514.toContract = some c1514 := rfl

theorem checked1514 : check 4000 c1514 = true := by decide

def original1515 : RawOriginal := C011.records[107]'(by decide)
theorem original_id1515 : original1515.index = 1515 := by decide

def c1515 : Contract := original1515.toContract.get (by decide)
theorem binding1515 : original1515.toContract = some c1515 := rfl

theorem checked1515 : check 4000 c1515 = true := by decide

def original1516 : RawOriginal := C011.records[108]'(by decide)
theorem original_id1516 : original1516.index = 1516 := by decide

def c1516 : Contract := original1516.toContract.get (by decide)
theorem binding1516 : original1516.toContract = some c1516 := rfl

theorem checked1516 : check 4000 c1516 = true := by decide

def original1517 : RawOriginal := C011.records[109]'(by decide)
theorem original_id1517 : original1517.index = 1517 := by decide

def c1517 : Contract := original1517.toContract.get (by decide)
theorem binding1517 : original1517.toContract = some c1517 := rfl

theorem checked1517 : check 4000 c1517 = true := by decide

def original1518 : RawOriginal := C011.records[110]'(by decide)
theorem original_id1518 : original1518.index = 1518 := by decide

def c1518 : Contract := original1518.toContract.get (by decide)
theorem binding1518 : original1518.toContract = some c1518 := rfl

theorem checked1518 : check 4000 c1518 = true := by decide

def original1519 : RawOriginal := C011.records[111]'(by decide)
theorem original_id1519 : original1519.index = 1519 := by decide

def c1519 : Contract := original1519.toContract.get (by decide)
theorem binding1519 : original1519.toContract = some c1519 := rfl

theorem checked1519 : check 4000 c1519 = true := by decide

def original1520 : RawOriginal := C011.records[112]'(by decide)
theorem original_id1520 : original1520.index = 1520 := by decide

def c1520 : Contract := original1520.toContract.get (by decide)
theorem binding1520 : original1520.toContract = some c1520 := rfl

theorem checked1520 : check 4000 c1520 = true := by decide

def original1521 : RawOriginal := C011.records[113]'(by decide)
theorem original_id1521 : original1521.index = 1521 := by decide

def c1521 : Contract := original1521.toContract.get (by decide)
theorem binding1521 : original1521.toContract = some c1521 := rfl

theorem checked1521 : check 4000 c1521 = true := by decide

def original1522 : RawOriginal := C011.records[114]'(by decide)
theorem original_id1522 : original1522.index = 1522 := by decide

def c1522 : Contract := original1522.toContract.get (by decide)
theorem binding1522 : original1522.toContract = some c1522 := rfl

theorem checked1522 : check 4000 c1522 = true := by decide

def original1523 : RawOriginal := C011.records[115]'(by decide)
theorem original_id1523 : original1523.index = 1523 := by decide

def c1523 : Contract := original1523.toContract.get (by decide)
theorem binding1523 : original1523.toContract = some c1523 := rfl

theorem checked1523 : check 4000 c1523 = true := by decide

def original1524 : RawOriginal := C011.records[116]'(by decide)
theorem original_id1524 : original1524.index = 1524 := by decide

def c1524 : Contract := original1524.toContract.get (by decide)
theorem binding1524 : original1524.toContract = some c1524 := rfl

theorem checked1524 : check 4000 c1524 = true := by decide

def original1525 : RawOriginal := C011.records[117]'(by decide)
theorem original_id1525 : original1525.index = 1525 := by decide

def c1525 : Contract := original1525.toContract.get (by decide)
theorem binding1525 : original1525.toContract = some c1525 := rfl

theorem checked1525 : check 4000 c1525 = true := by decide

def records : List Certified := [
  ⟨1510, c1510, 4000, checked1510⟩,
  ⟨1511, c1511, 4000, checked1511⟩,
  ⟨1512, c1512, 4000, checked1512⟩,
  ⟨1513, c1513, 4000, checked1513⟩,
  ⟨1514, c1514, 4000, checked1514⟩,
  ⟨1515, c1515, 4000, checked1515⟩,
  ⟨1516, c1516, 4000, checked1516⟩,
  ⟨1517, c1517, 4000, checked1517⟩,
  ⟨1518, c1518, 4000, checked1518⟩,
  ⟨1519, c1519, 4000, checked1519⟩,
  ⟨1520, c1520, 4000, checked1520⟩,
  ⟨1521, c1521, 4000, checked1521⟩,
  ⟨1522, c1522, 4000, checked1522⟩,
  ⟨1523, c1523, 4000, checked1523⟩,
  ⟨1524, c1524, 4000, checked1524⟩,
  ⟨1525, c1525, 4000, checked1525⟩]

end PA215.ContractShards.Shard011Part6
