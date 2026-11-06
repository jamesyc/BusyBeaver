import PA215.CertifiedContracts
import PA215.Census.C013
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard013Part3
open PA215.Contracts PA215.Census

def original1718 : RawOriginal := C013.records[54]'(by decide)
theorem original_id1718 : original1718.index = 1718 := by decide

def c1718 : Contract := original1718.toContract.get (by decide)
theorem binding1718 : original1718.toContract = some c1718 := rfl

theorem checked1718 : check 4000 c1718 = true := by decide

def original1719 : RawOriginal := C013.records[55]'(by decide)
theorem original_id1719 : original1719.index = 1719 := by decide

def c1719 : Contract := original1719.toContract.get (by decide)
theorem binding1719 : original1719.toContract = some c1719 := rfl

theorem checked1719 : check 4000 c1719 = true := by decide

def original1720 : RawOriginal := C013.records[56]'(by decide)
theorem original_id1720 : original1720.index = 1720 := by decide

def c1720 : Contract := original1720.toContract.get (by decide)
theorem binding1720 : original1720.toContract = some c1720 := rfl

theorem checked1720 : check 4000 c1720 = true := by decide

def original1721 : RawOriginal := C013.records[57]'(by decide)
theorem original_id1721 : original1721.index = 1721 := by decide

def c1721 : Contract := original1721.toContract.get (by decide)
theorem binding1721 : original1721.toContract = some c1721 := rfl

theorem checked1721 : check 4000 c1721 = true := by decide

def original1722 : RawOriginal := C013.records[58]'(by decide)
theorem original_id1722 : original1722.index = 1722 := by decide

def c1722 : Contract := original1722.toContract.get (by decide)
theorem binding1722 : original1722.toContract = some c1722 := rfl

theorem checked1722 : check 4000 c1722 = true := by decide

def original1723 : RawOriginal := C013.records[59]'(by decide)
theorem original_id1723 : original1723.index = 1723 := by decide

def c1723 : Contract := original1723.toContract.get (by decide)
theorem binding1723 : original1723.toContract = some c1723 := rfl

theorem checked1723 : check 4000 c1723 = true := by decide

def original1724 : RawOriginal := C013.records[60]'(by decide)
theorem original_id1724 : original1724.index = 1724 := by decide

def c1724 : Contract := original1724.toContract.get (by decide)
theorem binding1724 : original1724.toContract = some c1724 := rfl

theorem checked1724 : check 4000 c1724 = true := by decide

def original1725 : RawOriginal := C013.records[61]'(by decide)
theorem original_id1725 : original1725.index = 1725 := by decide

def c1725 : Contract := original1725.toContract.get (by decide)
theorem binding1725 : original1725.toContract = some c1725 := rfl

theorem checked1725 : check 4000 c1725 = true := by decide

def original1726 : RawOriginal := C013.records[62]'(by decide)
theorem original_id1726 : original1726.index = 1726 := by decide

def c1726 : Contract := original1726.toContract.get (by decide)
theorem binding1726 : original1726.toContract = some c1726 := rfl

theorem checked1726 : check 4000 c1726 = true := by decide

def original1727 : RawOriginal := C013.records[63]'(by decide)
theorem original_id1727 : original1727.index = 1727 := by decide

def c1727 : Contract := original1727.toContract.get (by decide)
theorem binding1727 : original1727.toContract = some c1727 := rfl

theorem checked1727 : check 4000 c1727 = true := by decide

def original1728 : RawOriginal := C013.records[64]'(by decide)
theorem original_id1728 : original1728.index = 1728 := by decide

def c1728 : Contract := original1728.toContract.get (by decide)
theorem binding1728 : original1728.toContract = some c1728 := rfl

theorem checked1728 : check 4000 c1728 = true := by decide

def original1729 : RawOriginal := C013.records[65]'(by decide)
theorem original_id1729 : original1729.index = 1729 := by decide

def c1729 : Contract := original1729.toContract.get (by decide)
theorem binding1729 : original1729.toContract = some c1729 := rfl

theorem checked1729 : check 4000 c1729 = true := by decide

def original1730 : RawOriginal := C013.records[66]'(by decide)
theorem original_id1730 : original1730.index = 1730 := by decide

def c1730 : Contract := original1730.toContract.get (by decide)
theorem binding1730 : original1730.toContract = some c1730 := rfl

theorem checked1730 : check 4000 c1730 = true := by decide

def original1731 : RawOriginal := C013.records[67]'(by decide)
theorem original_id1731 : original1731.index = 1731 := by decide

def c1731 : Contract := original1731.toContract.get (by decide)
theorem binding1731 : original1731.toContract = some c1731 := rfl

theorem checked1731 : check 4000 c1731 = true := by decide

def original1732 : RawOriginal := C013.records[68]'(by decide)
theorem original_id1732 : original1732.index = 1732 := by decide

def c1732 : Contract := original1732.toContract.get (by decide)
theorem binding1732 : original1732.toContract = some c1732 := rfl

theorem checked1732 : check 4000 c1732 = true := by decide

def original1733 : RawOriginal := C013.records[69]'(by decide)
theorem original_id1733 : original1733.index = 1733 := by decide

def c1733 : Contract := original1733.toContract.get (by decide)
theorem binding1733 : original1733.toContract = some c1733 := rfl

theorem checked1733 : check 4000 c1733 = true := by decide

def records : List Certified := [
  ⟨1718, c1718, 4000, checked1718⟩,
  ⟨1719, c1719, 4000, checked1719⟩,
  ⟨1720, c1720, 4000, checked1720⟩,
  ⟨1721, c1721, 4000, checked1721⟩,
  ⟨1722, c1722, 4000, checked1722⟩,
  ⟨1723, c1723, 4000, checked1723⟩,
  ⟨1724, c1724, 4000, checked1724⟩,
  ⟨1725, c1725, 4000, checked1725⟩,
  ⟨1726, c1726, 4000, checked1726⟩,
  ⟨1727, c1727, 4000, checked1727⟩,
  ⟨1728, c1728, 4000, checked1728⟩,
  ⟨1729, c1729, 4000, checked1729⟩,
  ⟨1730, c1730, 4000, checked1730⟩,
  ⟨1731, c1731, 4000, checked1731⟩,
  ⟨1732, c1732, 4000, checked1732⟩,
  ⟨1733, c1733, 4000, checked1733⟩]

end PA215.ContractShards.Shard013Part3
