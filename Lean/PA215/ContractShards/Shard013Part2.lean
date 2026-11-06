import PA215.CertifiedContracts
import PA215.Census.C013
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard013Part2
open PA215.Contracts PA215.Census

def original1702 : RawOriginal := C013.records[38]'(by decide)
theorem original_id1702 : original1702.index = 1702 := by decide

def c1702 : Contract := original1702.toContract.get (by decide)
theorem binding1702 : original1702.toContract = some c1702 := rfl

theorem checked1702 : check 4000 c1702 = true := by decide

def original1703 : RawOriginal := C013.records[39]'(by decide)
theorem original_id1703 : original1703.index = 1703 := by decide

def c1703 : Contract := original1703.toContract.get (by decide)
theorem binding1703 : original1703.toContract = some c1703 := rfl

theorem checked1703 : check 4000 c1703 = true := by decide

def original1704 : RawOriginal := C013.records[40]'(by decide)
theorem original_id1704 : original1704.index = 1704 := by decide

def c1704 : Contract := original1704.toContract.get (by decide)
theorem binding1704 : original1704.toContract = some c1704 := rfl

theorem checked1704 : check 4000 c1704 = true := by decide

def original1705 : RawOriginal := C013.records[41]'(by decide)
theorem original_id1705 : original1705.index = 1705 := by decide

def c1705 : Contract := original1705.toContract.get (by decide)
theorem binding1705 : original1705.toContract = some c1705 := rfl

theorem checked1705 : check 4000 c1705 = true := by decide

def original1706 : RawOriginal := C013.records[42]'(by decide)
theorem original_id1706 : original1706.index = 1706 := by decide

def c1706 : Contract := original1706.toContract.get (by decide)
theorem binding1706 : original1706.toContract = some c1706 := rfl

theorem checked1706 : check 4000 c1706 = true := by decide

def original1707 : RawOriginal := C013.records[43]'(by decide)
theorem original_id1707 : original1707.index = 1707 := by decide

def c1707 : Contract := original1707.toContract.get (by decide)
theorem binding1707 : original1707.toContract = some c1707 := rfl

theorem checked1707 : check 4000 c1707 = true := by decide

def original1708 : RawOriginal := C013.records[44]'(by decide)
theorem original_id1708 : original1708.index = 1708 := by decide

def c1708 : Contract := original1708.toContract.get (by decide)
theorem binding1708 : original1708.toContract = some c1708 := rfl

theorem checked1708 : check 4000 c1708 = true := by decide

def original1709 : RawOriginal := C013.records[45]'(by decide)
theorem original_id1709 : original1709.index = 1709 := by decide

def c1709 : Contract := original1709.toContract.get (by decide)
theorem binding1709 : original1709.toContract = some c1709 := rfl

theorem checked1709 : check 4000 c1709 = true := by decide

def original1710 : RawOriginal := C013.records[46]'(by decide)
theorem original_id1710 : original1710.index = 1710 := by decide

def c1710 : Contract := original1710.toContract.get (by decide)
theorem binding1710 : original1710.toContract = some c1710 := rfl

theorem checked1710 : check 4000 c1710 = true := by decide

def original1711 : RawOriginal := C013.records[47]'(by decide)
theorem original_id1711 : original1711.index = 1711 := by decide

def c1711 : Contract := original1711.toContract.get (by decide)
theorem binding1711 : original1711.toContract = some c1711 := rfl

theorem checked1711 : check 4000 c1711 = true := by decide

def original1712 : RawOriginal := C013.records[48]'(by decide)
theorem original_id1712 : original1712.index = 1712 := by decide

def c1712 : Contract := original1712.toContract.get (by decide)
theorem binding1712 : original1712.toContract = some c1712 := rfl

theorem checked1712 : check 4000 c1712 = true := by decide

def original1713 : RawOriginal := C013.records[49]'(by decide)
theorem original_id1713 : original1713.index = 1713 := by decide

def c1713 : Contract := original1713.toContract.get (by decide)
theorem binding1713 : original1713.toContract = some c1713 := rfl

theorem checked1713 : check 4000 c1713 = true := by decide

def original1714 : RawOriginal := C013.records[50]'(by decide)
theorem original_id1714 : original1714.index = 1714 := by decide

def c1714 : Contract := original1714.toContract.get (by decide)
theorem binding1714 : original1714.toContract = some c1714 := rfl

theorem checked1714 : check 4000 c1714 = true := by decide

def original1715 : RawOriginal := C013.records[51]'(by decide)
theorem original_id1715 : original1715.index = 1715 := by decide

def c1715 : Contract := original1715.toContract.get (by decide)
theorem binding1715 : original1715.toContract = some c1715 := rfl

theorem checked1715 : check 4000 c1715 = true := by decide

def original1716 : RawOriginal := C013.records[52]'(by decide)
theorem original_id1716 : original1716.index = 1716 := by decide

def c1716 : Contract := original1716.toContract.get (by decide)
theorem binding1716 : original1716.toContract = some c1716 := rfl

theorem checked1716 : check 4000 c1716 = true := by decide

def original1717 : RawOriginal := C013.records[53]'(by decide)
theorem original_id1717 : original1717.index = 1717 := by decide

def c1717 : Contract := original1717.toContract.get (by decide)
theorem binding1717 : original1717.toContract = some c1717 := rfl

theorem checked1717 : check 4000 c1717 = true := by decide

def records : List Certified := [
  ⟨1702, c1702, 4000, checked1702⟩,
  ⟨1703, c1703, 4000, checked1703⟩,
  ⟨1704, c1704, 4000, checked1704⟩,
  ⟨1705, c1705, 4000, checked1705⟩,
  ⟨1706, c1706, 4000, checked1706⟩,
  ⟨1707, c1707, 4000, checked1707⟩,
  ⟨1708, c1708, 4000, checked1708⟩,
  ⟨1709, c1709, 4000, checked1709⟩,
  ⟨1710, c1710, 4000, checked1710⟩,
  ⟨1711, c1711, 4000, checked1711⟩,
  ⟨1712, c1712, 4000, checked1712⟩,
  ⟨1713, c1713, 4000, checked1713⟩,
  ⟨1714, c1714, 4000, checked1714⟩,
  ⟨1715, c1715, 4000, checked1715⟩,
  ⟨1716, c1716, 4000, checked1716⟩,
  ⟨1717, c1717, 4000, checked1717⟩]

end PA215.ContractShards.Shard013Part2
