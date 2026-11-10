import PA215.CertifiedContracts
import PA215.Census.C012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard012Part1
open PA215.Contracts PA215.Census

def original1558 : RawOriginal := C012.records[22]'(by decide)
theorem original_id1558 : original1558.index = 1558 := by decide

def c1558 : Contract := original1558.toContract.get (by decide)
theorem binding1558 : original1558.toContract = some c1558 := rfl

theorem checked1558 : check 4000 c1558 = true := by decide

def original1559 : RawOriginal := C012.records[23]'(by decide)
theorem original_id1559 : original1559.index = 1559 := by decide

def c1559 : Contract := original1559.toContract.get (by decide)
theorem binding1559 : original1559.toContract = some c1559 := rfl

theorem checked1559 : check 4000 c1559 = true := by decide

def original1560 : RawOriginal := C012.records[24]'(by decide)
theorem original_id1560 : original1560.index = 1560 := by decide

def c1560 : Contract := original1560.toContract.get (by decide)
theorem binding1560 : original1560.toContract = some c1560 := rfl

theorem checked1560 : check 4000 c1560 = true := by decide

def original1561 : RawOriginal := C012.records[25]'(by decide)
theorem original_id1561 : original1561.index = 1561 := by decide

def c1561 : Contract := original1561.toContract.get (by decide)
theorem binding1561 : original1561.toContract = some c1561 := rfl

theorem checked1561 : check 4000 c1561 = true := by decide

def original1562 : RawOriginal := C012.records[26]'(by decide)
theorem original_id1562 : original1562.index = 1562 := by decide

def c1562 : Contract := original1562.toContract.get (by decide)
theorem binding1562 : original1562.toContract = some c1562 := rfl

theorem checked1562 : check 4000 c1562 = true := by decide

def original1563 : RawOriginal := C012.records[27]'(by decide)
theorem original_id1563 : original1563.index = 1563 := by decide

def c1563 : Contract := original1563.toContract.get (by decide)
theorem binding1563 : original1563.toContract = some c1563 := rfl

theorem checked1563 : check 4000 c1563 = true := by decide

def original1564 : RawOriginal := C012.records[28]'(by decide)
theorem original_id1564 : original1564.index = 1564 := by decide

def c1564 : Contract := original1564.toContract.get (by decide)
theorem binding1564 : original1564.toContract = some c1564 := rfl

theorem checked1564 : check 4000 c1564 = true := by decide

def original1565 : RawOriginal := C012.records[29]'(by decide)
theorem original_id1565 : original1565.index = 1565 := by decide

def c1565 : Contract := original1565.toContract.get (by decide)
theorem binding1565 : original1565.toContract = some c1565 := rfl

theorem checked1565 : check 4000 c1565 = true := by decide

def original1566 : RawOriginal := C012.records[30]'(by decide)
theorem original_id1566 : original1566.index = 1566 := by decide

def c1566 : Contract := original1566.toContract.get (by decide)
theorem binding1566 : original1566.toContract = some c1566 := rfl

theorem checked1566 : check 4000 c1566 = true := by decide

def original1567 : RawOriginal := C012.records[31]'(by decide)
theorem original_id1567 : original1567.index = 1567 := by decide

def c1567 : Contract := original1567.toContract.get (by decide)
theorem binding1567 : original1567.toContract = some c1567 := rfl

theorem checked1567 : check 4000 c1567 = true := by decide

def original1568 : RawOriginal := C012.records[32]'(by decide)
theorem original_id1568 : original1568.index = 1568 := by decide

def c1568 : Contract := original1568.toContract.get (by decide)
theorem binding1568 : original1568.toContract = some c1568 := rfl

theorem checked1568 : check 4000 c1568 = true := by decide

def original1569 : RawOriginal := C012.records[33]'(by decide)
theorem original_id1569 : original1569.index = 1569 := by decide

def c1569 : Contract := original1569.toContract.get (by decide)
theorem binding1569 : original1569.toContract = some c1569 := rfl

theorem checked1569 : check 4000 c1569 = true := by decide

def original1570 : RawOriginal := C012.records[34]'(by decide)
theorem original_id1570 : original1570.index = 1570 := by decide

def c1570 : Contract := original1570.toContract.get (by decide)
theorem binding1570 : original1570.toContract = some c1570 := rfl

theorem checked1570 : check 4000 c1570 = true := by decide

def original1571 : RawOriginal := C012.records[35]'(by decide)
theorem original_id1571 : original1571.index = 1571 := by decide

def c1571 : Contract := original1571.toContract.get (by decide)
theorem binding1571 : original1571.toContract = some c1571 := rfl

theorem checked1571 : check 4000 c1571 = true := by decide

def original1572 : RawOriginal := C012.records[36]'(by decide)
theorem original_id1572 : original1572.index = 1572 := by decide

def c1572 : Contract := original1572.toContract.get (by decide)
theorem binding1572 : original1572.toContract = some c1572 := rfl

theorem checked1572 : check 4000 c1572 = true := by decide

def original1573 : RawOriginal := C012.records[37]'(by decide)
theorem original_id1573 : original1573.index = 1573 := by decide

def c1573 : Contract := original1573.toContract.get (by decide)
theorem binding1573 : original1573.toContract = some c1573 := rfl

theorem checked1573 : check 4000 c1573 = true := by decide

def records : List Certified := [
  ⟨1558, c1558, 4000, checked1558⟩,
  ⟨1559, c1559, 4000, checked1559⟩,
  ⟨1560, c1560, 4000, checked1560⟩,
  ⟨1561, c1561, 4000, checked1561⟩,
  ⟨1562, c1562, 4000, checked1562⟩,
  ⟨1563, c1563, 4000, checked1563⟩,
  ⟨1564, c1564, 4000, checked1564⟩,
  ⟨1565, c1565, 4000, checked1565⟩,
  ⟨1566, c1566, 4000, checked1566⟩,
  ⟨1567, c1567, 4000, checked1567⟩,
  ⟨1568, c1568, 4000, checked1568⟩,
  ⟨1569, c1569, 4000, checked1569⟩,
  ⟨1570, c1570, 4000, checked1570⟩,
  ⟨1571, c1571, 4000, checked1571⟩,
  ⟨1572, c1572, 4000, checked1572⟩,
  ⟨1573, c1573, 4000, checked1573⟩]

end PA215.ContractShards.Shard012Part1
