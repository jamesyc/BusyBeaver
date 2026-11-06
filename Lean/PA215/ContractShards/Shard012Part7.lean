import PA215.CertifiedContracts
import PA215.Census.C012
import PA215.Census.C013
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard012Part7
open PA215.Contracts PA215.Census

def original1654 : RawOriginal := C012.records[118]'(by decide)
theorem original_id1654 : original1654.index = 1654 := by decide

def c1654 : Contract := original1654.toContract.get (by decide)
theorem binding1654 : original1654.toContract = some c1654 := rfl

theorem checked1654 : check 4000 c1654 = true := by decide

def original1655 : RawOriginal := C012.records[119]'(by decide)
theorem original_id1655 : original1655.index = 1655 := by decide

def c1655 : Contract := original1655.toContract.get (by decide)
theorem binding1655 : original1655.toContract = some c1655 := rfl

theorem checked1655 : check 4000 c1655 = true := by decide

def original1656 : RawOriginal := C012.records[120]'(by decide)
theorem original_id1656 : original1656.index = 1656 := by decide

def c1656 : Contract := original1656.toContract.get (by decide)
theorem binding1656 : original1656.toContract = some c1656 := rfl

theorem checked1656 : check 4000 c1656 = true := by decide

def original1657 : RawOriginal := C012.records[121]'(by decide)
theorem original_id1657 : original1657.index = 1657 := by decide

def c1657 : Contract := original1657.toContract.get (by decide)
theorem binding1657 : original1657.toContract = some c1657 := rfl

theorem checked1657 : check 4000 c1657 = true := by decide

def original1658 : RawOriginal := C012.records[122]'(by decide)
theorem original_id1658 : original1658.index = 1658 := by decide

def c1658 : Contract := original1658.toContract.get (by decide)
theorem binding1658 : original1658.toContract = some c1658 := rfl

theorem checked1658 : check 4000 c1658 = true := by decide

def original1659 : RawOriginal := C012.records[123]'(by decide)
theorem original_id1659 : original1659.index = 1659 := by decide

def c1659 : Contract := original1659.toContract.get (by decide)
theorem binding1659 : original1659.toContract = some c1659 := rfl

theorem checked1659 : check 4000 c1659 = true := by decide

def original1660 : RawOriginal := C012.records[124]'(by decide)
theorem original_id1660 : original1660.index = 1660 := by decide

def c1660 : Contract := original1660.toContract.get (by decide)
theorem binding1660 : original1660.toContract = some c1660 := rfl

theorem checked1660 : check 4000 c1660 = true := by decide

def original1661 : RawOriginal := C012.records[125]'(by decide)
theorem original_id1661 : original1661.index = 1661 := by decide

def c1661 : Contract := original1661.toContract.get (by decide)
theorem binding1661 : original1661.toContract = some c1661 := rfl

theorem checked1661 : check 4000 c1661 = true := by decide

def original1662 : RawOriginal := C012.records[126]'(by decide)
theorem original_id1662 : original1662.index = 1662 := by decide

def c1662 : Contract := original1662.toContract.get (by decide)
theorem binding1662 : original1662.toContract = some c1662 := rfl

theorem checked1662 : check 4000 c1662 = true := by decide

def original1663 : RawOriginal := C012.records[127]'(by decide)
theorem original_id1663 : original1663.index = 1663 := by decide

def c1663 : Contract := original1663.toContract.get (by decide)
theorem binding1663 : original1663.toContract = some c1663 := rfl

theorem checked1663 : check 4000 c1663 = true := by decide

def original1664 : RawOriginal := C013.records[0]'(by decide)
theorem original_id1664 : original1664.index = 1664 := by decide

def c1664 : Contract := original1664.toContract.get (by decide)
theorem binding1664 : original1664.toContract = some c1664 := rfl

theorem checked1664 : check 4000 c1664 = true := by decide

def original1665 : RawOriginal := C013.records[1]'(by decide)
theorem original_id1665 : original1665.index = 1665 := by decide

def c1665 : Contract := original1665.toContract.get (by decide)
theorem binding1665 : original1665.toContract = some c1665 := rfl

theorem checked1665 : check 4000 c1665 = true := by decide

def original1666 : RawOriginal := C013.records[2]'(by decide)
theorem original_id1666 : original1666.index = 1666 := by decide

def c1666 : Contract := original1666.toContract.get (by decide)
theorem binding1666 : original1666.toContract = some c1666 := rfl

theorem checked1666 : check 4000 c1666 = true := by decide

def original1667 : RawOriginal := C013.records[3]'(by decide)
theorem original_id1667 : original1667.index = 1667 := by decide

def c1667 : Contract := original1667.toContract.get (by decide)
theorem binding1667 : original1667.toContract = some c1667 := rfl

theorem checked1667 : check 4000 c1667 = true := by decide

def original1668 : RawOriginal := C013.records[4]'(by decide)
theorem original_id1668 : original1668.index = 1668 := by decide

def c1668 : Contract := original1668.toContract.get (by decide)
theorem binding1668 : original1668.toContract = some c1668 := rfl

theorem checked1668 : check 4000 c1668 = true := by decide

def original1669 : RawOriginal := C013.records[5]'(by decide)
theorem original_id1669 : original1669.index = 1669 := by decide

def c1669 : Contract := original1669.toContract.get (by decide)
theorem binding1669 : original1669.toContract = some c1669 := rfl

theorem checked1669 : check 4000 c1669 = true := by decide

def records : List Certified := [
  ⟨1654, c1654, 4000, checked1654⟩,
  ⟨1655, c1655, 4000, checked1655⟩,
  ⟨1656, c1656, 4000, checked1656⟩,
  ⟨1657, c1657, 4000, checked1657⟩,
  ⟨1658, c1658, 4000, checked1658⟩,
  ⟨1659, c1659, 4000, checked1659⟩,
  ⟨1660, c1660, 4000, checked1660⟩,
  ⟨1661, c1661, 4000, checked1661⟩,
  ⟨1662, c1662, 4000, checked1662⟩,
  ⟨1663, c1663, 4000, checked1663⟩,
  ⟨1664, c1664, 4000, checked1664⟩,
  ⟨1665, c1665, 4000, checked1665⟩,
  ⟨1666, c1666, 4000, checked1666⟩,
  ⟨1667, c1667, 4000, checked1667⟩,
  ⟨1668, c1668, 4000, checked1668⟩,
  ⟨1669, c1669, 4000, checked1669⟩]

end PA215.ContractShards.Shard012Part7
