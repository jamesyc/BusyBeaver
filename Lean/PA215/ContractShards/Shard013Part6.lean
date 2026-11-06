import PA215.CertifiedContracts
import PA215.Census.C013
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard013Part6
open PA215.Contracts PA215.Census

def original1766 : RawOriginal := C013.records[102]'(by decide)
theorem original_id1766 : original1766.index = 1766 := by decide

def c1766 : Contract := original1766.toContract.get (by decide)
theorem binding1766 : original1766.toContract = some c1766 := rfl

theorem checked1766 : check 4000 c1766 = true := by decide

def original1767 : RawOriginal := C013.records[103]'(by decide)
theorem original_id1767 : original1767.index = 1767 := by decide

def c1767 : Contract := original1767.toContract.get (by decide)
theorem binding1767 : original1767.toContract = some c1767 := rfl

theorem checked1767 : check 4000 c1767 = true := by decide

def original1768 : RawOriginal := C013.records[104]'(by decide)
theorem original_id1768 : original1768.index = 1768 := by decide

def c1768 : Contract := original1768.toContract.get (by decide)
theorem binding1768 : original1768.toContract = some c1768 := rfl

theorem checked1768 : check 4000 c1768 = true := by decide

def original1769 : RawOriginal := C013.records[105]'(by decide)
theorem original_id1769 : original1769.index = 1769 := by decide

def c1769 : Contract := original1769.toContract.get (by decide)
theorem binding1769 : original1769.toContract = some c1769 := rfl

theorem checked1769 : check 4000 c1769 = true := by decide

def original1770 : RawOriginal := C013.records[106]'(by decide)
theorem original_id1770 : original1770.index = 1770 := by decide

def c1770 : Contract := original1770.toContract.get (by decide)
theorem binding1770 : original1770.toContract = some c1770 := rfl

theorem checked1770 : check 4000 c1770 = true := by decide

def original1771 : RawOriginal := C013.records[107]'(by decide)
theorem original_id1771 : original1771.index = 1771 := by decide

def c1771 : Contract := original1771.toContract.get (by decide)
theorem binding1771 : original1771.toContract = some c1771 := rfl

theorem checked1771 : check 4000 c1771 = true := by decide

def original1772 : RawOriginal := C013.records[108]'(by decide)
theorem original_id1772 : original1772.index = 1772 := by decide

def c1772 : Contract := original1772.toContract.get (by decide)
theorem binding1772 : original1772.toContract = some c1772 := rfl

theorem checked1772 : check 4000 c1772 = true := by decide

def original1773 : RawOriginal := C013.records[109]'(by decide)
theorem original_id1773 : original1773.index = 1773 := by decide

def c1773 : Contract := original1773.toContract.get (by decide)
theorem binding1773 : original1773.toContract = some c1773 := rfl

theorem checked1773 : check 4000 c1773 = true := by decide

def original1774 : RawOriginal := C013.records[110]'(by decide)
theorem original_id1774 : original1774.index = 1774 := by decide

def c1774 : Contract := original1774.toContract.get (by decide)
theorem binding1774 : original1774.toContract = some c1774 := rfl

theorem checked1774 : check 4000 c1774 = true := by decide

def original1775 : RawOriginal := C013.records[111]'(by decide)
theorem original_id1775 : original1775.index = 1775 := by decide

def c1775 : Contract := original1775.toContract.get (by decide)
theorem binding1775 : original1775.toContract = some c1775 := rfl

theorem checked1775 : check 4000 c1775 = true := by decide

def original1776 : RawOriginal := C013.records[112]'(by decide)
theorem original_id1776 : original1776.index = 1776 := by decide

def c1776 : Contract := original1776.toContract.get (by decide)
theorem binding1776 : original1776.toContract = some c1776 := rfl

theorem checked1776 : check 4000 c1776 = true := by decide

def original1777 : RawOriginal := C013.records[113]'(by decide)
theorem original_id1777 : original1777.index = 1777 := by decide

def c1777 : Contract := original1777.toContract.get (by decide)
theorem binding1777 : original1777.toContract = some c1777 := rfl

theorem checked1777 : check 4000 c1777 = true := by decide

def original1778 : RawOriginal := C013.records[114]'(by decide)
theorem original_id1778 : original1778.index = 1778 := by decide

def c1778 : Contract := original1778.toContract.get (by decide)
theorem binding1778 : original1778.toContract = some c1778 := rfl

theorem checked1778 : check 4000 c1778 = true := by decide

def original1779 : RawOriginal := C013.records[115]'(by decide)
theorem original_id1779 : original1779.index = 1779 := by decide

def c1779 : Contract := original1779.toContract.get (by decide)
theorem binding1779 : original1779.toContract = some c1779 := rfl

theorem checked1779 : check 4000 c1779 = true := by decide

def original1780 : RawOriginal := C013.records[116]'(by decide)
theorem original_id1780 : original1780.index = 1780 := by decide

def c1780 : Contract := original1780.toContract.get (by decide)
theorem binding1780 : original1780.toContract = some c1780 := rfl

theorem checked1780 : check 4000 c1780 = true := by decide

def original1781 : RawOriginal := C013.records[117]'(by decide)
theorem original_id1781 : original1781.index = 1781 := by decide

def c1781 : Contract := original1781.toContract.get (by decide)
theorem binding1781 : original1781.toContract = some c1781 := rfl

theorem checked1781 : check 4000 c1781 = true := by decide

def records : List Certified := [
  ⟨1766, c1766, 4000, checked1766⟩,
  ⟨1767, c1767, 4000, checked1767⟩,
  ⟨1768, c1768, 4000, checked1768⟩,
  ⟨1769, c1769, 4000, checked1769⟩,
  ⟨1770, c1770, 4000, checked1770⟩,
  ⟨1771, c1771, 4000, checked1771⟩,
  ⟨1772, c1772, 4000, checked1772⟩,
  ⟨1773, c1773, 4000, checked1773⟩,
  ⟨1774, c1774, 4000, checked1774⟩,
  ⟨1775, c1775, 4000, checked1775⟩,
  ⟨1776, c1776, 4000, checked1776⟩,
  ⟨1777, c1777, 4000, checked1777⟩,
  ⟨1778, c1778, 4000, checked1778⟩,
  ⟨1779, c1779, 4000, checked1779⟩,
  ⟨1780, c1780, 4000, checked1780⟩,
  ⟨1781, c1781, 4000, checked1781⟩]

end PA215.ContractShards.Shard013Part6
