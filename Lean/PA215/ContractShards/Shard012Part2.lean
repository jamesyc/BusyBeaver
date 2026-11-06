import PA215.CertifiedContracts
import PA215.Census.C012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard012Part2
open PA215.Contracts PA215.Census

def original1574 : RawOriginal := C012.records[38]'(by decide)
theorem original_id1574 : original1574.index = 1574 := by decide

def c1574 : Contract := original1574.toContract.get (by decide)
theorem binding1574 : original1574.toContract = some c1574 := rfl

theorem checked1574 : check 4000 c1574 = true := by decide

def original1575 : RawOriginal := C012.records[39]'(by decide)
theorem original_id1575 : original1575.index = 1575 := by decide

def c1575 : Contract := original1575.toContract.get (by decide)
theorem binding1575 : original1575.toContract = some c1575 := rfl

theorem checked1575 : check 4000 c1575 = true := by decide

def original1576 : RawOriginal := C012.records[40]'(by decide)
theorem original_id1576 : original1576.index = 1576 := by decide

def c1576 : Contract := original1576.toContract.get (by decide)
theorem binding1576 : original1576.toContract = some c1576 := rfl

theorem checked1576 : check 4000 c1576 = true := by decide

def original1577 : RawOriginal := C012.records[41]'(by decide)
theorem original_id1577 : original1577.index = 1577 := by decide

def c1577 : Contract := original1577.toContract.get (by decide)
theorem binding1577 : original1577.toContract = some c1577 := rfl

theorem checked1577 : check 4000 c1577 = true := by decide

def original1578 : RawOriginal := C012.records[42]'(by decide)
theorem original_id1578 : original1578.index = 1578 := by decide

def c1578 : Contract := original1578.toContract.get (by decide)
theorem binding1578 : original1578.toContract = some c1578 := rfl

theorem checked1578 : check 4000 c1578 = true := by decide

def original1579 : RawOriginal := C012.records[43]'(by decide)
theorem original_id1579 : original1579.index = 1579 := by decide

def c1579 : Contract := original1579.toContract.get (by decide)
theorem binding1579 : original1579.toContract = some c1579 := rfl

theorem checked1579 : check 4000 c1579 = true := by decide

def original1580 : RawOriginal := C012.records[44]'(by decide)
theorem original_id1580 : original1580.index = 1580 := by decide

def c1580 : Contract := original1580.toContract.get (by decide)
theorem binding1580 : original1580.toContract = some c1580 := rfl

theorem checked1580 : check 4000 c1580 = true := by decide

def original1581 : RawOriginal := C012.records[45]'(by decide)
theorem original_id1581 : original1581.index = 1581 := by decide

def c1581 : Contract := original1581.toContract.get (by decide)
theorem binding1581 : original1581.toContract = some c1581 := rfl

theorem checked1581 : check 4000 c1581 = true := by decide

def original1582 : RawOriginal := C012.records[46]'(by decide)
theorem original_id1582 : original1582.index = 1582 := by decide

def c1582 : Contract := original1582.toContract.get (by decide)
theorem binding1582 : original1582.toContract = some c1582 := rfl

theorem checked1582 : check 4000 c1582 = true := by decide

def original1583 : RawOriginal := C012.records[47]'(by decide)
theorem original_id1583 : original1583.index = 1583 := by decide

def c1583 : Contract := original1583.toContract.get (by decide)
theorem binding1583 : original1583.toContract = some c1583 := rfl

theorem checked1583 : check 4000 c1583 = true := by decide

def original1584 : RawOriginal := C012.records[48]'(by decide)
theorem original_id1584 : original1584.index = 1584 := by decide

def c1584 : Contract := original1584.toContract.get (by decide)
theorem binding1584 : original1584.toContract = some c1584 := rfl

theorem checked1584 : check 4000 c1584 = true := by decide

def original1585 : RawOriginal := C012.records[49]'(by decide)
theorem original_id1585 : original1585.index = 1585 := by decide

def c1585 : Contract := original1585.toContract.get (by decide)
theorem binding1585 : original1585.toContract = some c1585 := rfl

theorem checked1585 : check 4000 c1585 = true := by decide

def original1586 : RawOriginal := C012.records[50]'(by decide)
theorem original_id1586 : original1586.index = 1586 := by decide

def c1586 : Contract := original1586.toContract.get (by decide)
theorem binding1586 : original1586.toContract = some c1586 := rfl

theorem checked1586 : check 4000 c1586 = true := by decide

def original1587 : RawOriginal := C012.records[51]'(by decide)
theorem original_id1587 : original1587.index = 1587 := by decide

def c1587 : Contract := original1587.toContract.get (by decide)
theorem binding1587 : original1587.toContract = some c1587 := rfl

theorem checked1587 : check 4000 c1587 = true := by decide

def original1588 : RawOriginal := C012.records[52]'(by decide)
theorem original_id1588 : original1588.index = 1588 := by decide

def c1588 : Contract := original1588.toContract.get (by decide)
theorem binding1588 : original1588.toContract = some c1588 := rfl

theorem checked1588 : check 4000 c1588 = true := by decide

def original1589 : RawOriginal := C012.records[53]'(by decide)
theorem original_id1589 : original1589.index = 1589 := by decide

def c1589 : Contract := original1589.toContract.get (by decide)
theorem binding1589 : original1589.toContract = some c1589 := rfl

theorem checked1589 : check 4000 c1589 = true := by decide

def records : List Certified := [
  ⟨1574, c1574, 4000, checked1574⟩,
  ⟨1575, c1575, 4000, checked1575⟩,
  ⟨1576, c1576, 4000, checked1576⟩,
  ⟨1577, c1577, 4000, checked1577⟩,
  ⟨1578, c1578, 4000, checked1578⟩,
  ⟨1579, c1579, 4000, checked1579⟩,
  ⟨1580, c1580, 4000, checked1580⟩,
  ⟨1581, c1581, 4000, checked1581⟩,
  ⟨1582, c1582, 4000, checked1582⟩,
  ⟨1583, c1583, 4000, checked1583⟩,
  ⟨1584, c1584, 4000, checked1584⟩,
  ⟨1585, c1585, 4000, checked1585⟩,
  ⟨1586, c1586, 4000, checked1586⟩,
  ⟨1587, c1587, 4000, checked1587⟩,
  ⟨1588, c1588, 4000, checked1588⟩,
  ⟨1589, c1589, 4000, checked1589⟩]

end PA215.ContractShards.Shard012Part2
