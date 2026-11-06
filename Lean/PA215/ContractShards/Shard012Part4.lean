import PA215.CertifiedContracts
import PA215.Census.C012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard012Part4
open PA215.Contracts PA215.Census

def original1606 : RawOriginal := C012.records[70]'(by decide)
theorem original_id1606 : original1606.index = 1606 := by decide

def c1606 : Contract := original1606.toContract.get (by decide)
theorem binding1606 : original1606.toContract = some c1606 := rfl

theorem checked1606 : check 4000 c1606 = true := by decide

def original1607 : RawOriginal := C012.records[71]'(by decide)
theorem original_id1607 : original1607.index = 1607 := by decide

def c1607 : Contract := original1607.toContract.get (by decide)
theorem binding1607 : original1607.toContract = some c1607 := rfl

theorem checked1607 : check 4000 c1607 = true := by decide

def original1608 : RawOriginal := C012.records[72]'(by decide)
theorem original_id1608 : original1608.index = 1608 := by decide

def c1608 : Contract := original1608.toContract.get (by decide)
theorem binding1608 : original1608.toContract = some c1608 := rfl

theorem checked1608 : check 4000 c1608 = true := by decide

def original1609 : RawOriginal := C012.records[73]'(by decide)
theorem original_id1609 : original1609.index = 1609 := by decide

def c1609 : Contract := original1609.toContract.get (by decide)
theorem binding1609 : original1609.toContract = some c1609 := rfl

theorem checked1609 : check 4000 c1609 = true := by decide

def original1610 : RawOriginal := C012.records[74]'(by decide)
theorem original_id1610 : original1610.index = 1610 := by decide

def c1610 : Contract := original1610.toContract.get (by decide)
theorem binding1610 : original1610.toContract = some c1610 := rfl

theorem checked1610 : check 4000 c1610 = true := by decide

def original1611 : RawOriginal := C012.records[75]'(by decide)
theorem original_id1611 : original1611.index = 1611 := by decide

def c1611 : Contract := original1611.toContract.get (by decide)
theorem binding1611 : original1611.toContract = some c1611 := rfl

theorem checked1611 : check 4000 c1611 = true := by decide

def original1612 : RawOriginal := C012.records[76]'(by decide)
theorem original_id1612 : original1612.index = 1612 := by decide

def c1612 : Contract := original1612.toContract.get (by decide)
theorem binding1612 : original1612.toContract = some c1612 := rfl

theorem checked1612 : check 4000 c1612 = true := by decide

def original1613 : RawOriginal := C012.records[77]'(by decide)
theorem original_id1613 : original1613.index = 1613 := by decide

def c1613 : Contract := original1613.toContract.get (by decide)
theorem binding1613 : original1613.toContract = some c1613 := rfl

theorem checked1613 : check 4000 c1613 = true := by decide

def original1614 : RawOriginal := C012.records[78]'(by decide)
theorem original_id1614 : original1614.index = 1614 := by decide

def c1614 : Contract := original1614.toContract.get (by decide)
theorem binding1614 : original1614.toContract = some c1614 := rfl

theorem checked1614 : check 4000 c1614 = true := by decide

def original1615 : RawOriginal := C012.records[79]'(by decide)
theorem original_id1615 : original1615.index = 1615 := by decide

def c1615 : Contract := original1615.toContract.get (by decide)
theorem binding1615 : original1615.toContract = some c1615 := rfl

theorem checked1615 : check 4000 c1615 = true := by decide

def original1616 : RawOriginal := C012.records[80]'(by decide)
theorem original_id1616 : original1616.index = 1616 := by decide

def c1616 : Contract := original1616.toContract.get (by decide)
theorem binding1616 : original1616.toContract = some c1616 := rfl

theorem checked1616 : check 4000 c1616 = true := by decide

def original1617 : RawOriginal := C012.records[81]'(by decide)
theorem original_id1617 : original1617.index = 1617 := by decide

def c1617 : Contract := original1617.toContract.get (by decide)
theorem binding1617 : original1617.toContract = some c1617 := rfl

theorem checked1617 : check 4000 c1617 = true := by decide

def original1618 : RawOriginal := C012.records[82]'(by decide)
theorem original_id1618 : original1618.index = 1618 := by decide

def c1618 : Contract := original1618.toContract.get (by decide)
theorem binding1618 : original1618.toContract = some c1618 := rfl

theorem checked1618 : check 4000 c1618 = true := by decide

def original1619 : RawOriginal := C012.records[83]'(by decide)
theorem original_id1619 : original1619.index = 1619 := by decide

def c1619 : Contract := original1619.toContract.get (by decide)
theorem binding1619 : original1619.toContract = some c1619 := rfl

theorem checked1619 : check 4000 c1619 = true := by decide

def original1620 : RawOriginal := C012.records[84]'(by decide)
theorem original_id1620 : original1620.index = 1620 := by decide

def c1620 : Contract := original1620.toContract.get (by decide)
theorem binding1620 : original1620.toContract = some c1620 := rfl

theorem checked1620 : check 4000 c1620 = true := by decide

def original1621 : RawOriginal := C012.records[85]'(by decide)
theorem original_id1621 : original1621.index = 1621 := by decide

def c1621 : Contract := original1621.toContract.get (by decide)
theorem binding1621 : original1621.toContract = some c1621 := rfl

theorem checked1621 : check 4000 c1621 = true := by decide

def records : List Certified := [
  ⟨1606, c1606, 4000, checked1606⟩,
  ⟨1607, c1607, 4000, checked1607⟩,
  ⟨1608, c1608, 4000, checked1608⟩,
  ⟨1609, c1609, 4000, checked1609⟩,
  ⟨1610, c1610, 4000, checked1610⟩,
  ⟨1611, c1611, 4000, checked1611⟩,
  ⟨1612, c1612, 4000, checked1612⟩,
  ⟨1613, c1613, 4000, checked1613⟩,
  ⟨1614, c1614, 4000, checked1614⟩,
  ⟨1615, c1615, 4000, checked1615⟩,
  ⟨1616, c1616, 4000, checked1616⟩,
  ⟨1617, c1617, 4000, checked1617⟩,
  ⟨1618, c1618, 4000, checked1618⟩,
  ⟨1619, c1619, 4000, checked1619⟩,
  ⟨1620, c1620, 4000, checked1620⟩,
  ⟨1621, c1621, 4000, checked1621⟩]

end PA215.ContractShards.Shard012Part4
