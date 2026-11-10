import PA215.CertifiedContracts
import PA215.Census.C005
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard005Part5
open PA215.Contracts PA215.Census

def original726 : RawOriginal := C005.records[86]'(by decide)
theorem original_id726 : original726.index = 726 := by decide

def c726 : Contract := original726.toContract.get (by decide)
theorem binding726 : original726.toContract = some c726 := rfl

theorem checked726 : check 4000 c726 = true := by decide

def original727 : RawOriginal := C005.records[87]'(by decide)
theorem original_id727 : original727.index = 727 := by decide

def c727 : Contract := original727.toContract.get (by decide)
theorem binding727 : original727.toContract = some c727 := rfl

theorem checked727 : check 4000 c727 = true := by decide

def original728 : RawOriginal := C005.records[88]'(by decide)
theorem original_id728 : original728.index = 728 := by decide

def c728 : Contract := original728.toContract.get (by decide)
theorem binding728 : original728.toContract = some c728 := rfl

theorem checked728 : check 4000 c728 = true := by decide

def original729 : RawOriginal := C005.records[89]'(by decide)
theorem original_id729 : original729.index = 729 := by decide

def c729 : Contract := original729.toContract.get (by decide)
theorem binding729 : original729.toContract = some c729 := rfl

theorem checked729 : check 4000 c729 = true := by decide

def original730 : RawOriginal := C005.records[90]'(by decide)
theorem original_id730 : original730.index = 730 := by decide

def c730 : Contract := original730.toContract.get (by decide)
theorem binding730 : original730.toContract = some c730 := rfl

theorem checked730 : check 4000 c730 = true := by decide

def original731 : RawOriginal := C005.records[91]'(by decide)
theorem original_id731 : original731.index = 731 := by decide

def c731 : Contract := original731.toContract.get (by decide)
theorem binding731 : original731.toContract = some c731 := rfl

theorem checked731 : check 4000 c731 = true := by decide

def original732 : RawOriginal := C005.records[92]'(by decide)
theorem original_id732 : original732.index = 732 := by decide

def c732 : Contract := original732.toContract.get (by decide)
theorem binding732 : original732.toContract = some c732 := rfl

theorem checked732 : check 4000 c732 = true := by decide

def original733 : RawOriginal := C005.records[93]'(by decide)
theorem original_id733 : original733.index = 733 := by decide

def c733 : Contract := original733.toContract.get (by decide)
theorem binding733 : original733.toContract = some c733 := rfl

theorem checked733 : check 4000 c733 = true := by decide

def original734 : RawOriginal := C005.records[94]'(by decide)
theorem original_id734 : original734.index = 734 := by decide

def c734 : Contract := original734.toContract.get (by decide)
theorem binding734 : original734.toContract = some c734 := rfl

theorem checked734 : check 4000 c734 = true := by decide

def original735 : RawOriginal := C005.records[95]'(by decide)
theorem original_id735 : original735.index = 735 := by decide

def c735 : Contract := original735.toContract.get (by decide)
theorem binding735 : original735.toContract = some c735 := rfl

theorem checked735 : check 4000 c735 = true := by decide

def original736 : RawOriginal := C005.records[96]'(by decide)
theorem original_id736 : original736.index = 736 := by decide

def c736 : Contract := original736.toContract.get (by decide)
theorem binding736 : original736.toContract = some c736 := rfl

theorem checked736 : check 4000 c736 = true := by decide

def original737 : RawOriginal := C005.records[97]'(by decide)
theorem original_id737 : original737.index = 737 := by decide

def c737 : Contract := original737.toContract.get (by decide)
theorem binding737 : original737.toContract = some c737 := rfl

theorem checked737 : check 4000 c737 = true := by decide

def original738 : RawOriginal := C005.records[98]'(by decide)
theorem original_id738 : original738.index = 738 := by decide

def c738 : Contract := original738.toContract.get (by decide)
theorem binding738 : original738.toContract = some c738 := rfl

theorem checked738 : check 4000 c738 = true := by decide

def original739 : RawOriginal := C005.records[99]'(by decide)
theorem original_id739 : original739.index = 739 := by decide

def c739 : Contract := original739.toContract.get (by decide)
theorem binding739 : original739.toContract = some c739 := rfl

theorem checked739 : check 4000 c739 = true := by decide

def original740 : RawOriginal := C005.records[100]'(by decide)
theorem original_id740 : original740.index = 740 := by decide

def c740 : Contract := original740.toContract.get (by decide)
theorem binding740 : original740.toContract = some c740 := rfl

theorem checked740 : check 4000 c740 = true := by decide

def original741 : RawOriginal := C005.records[101]'(by decide)
theorem original_id741 : original741.index = 741 := by decide

def c741 : Contract := original741.toContract.get (by decide)
theorem binding741 : original741.toContract = some c741 := rfl

theorem checked741 : check 4000 c741 = true := by decide

def records : List Certified := [
  ⟨726, c726, 4000, checked726⟩,
  ⟨727, c727, 4000, checked727⟩,
  ⟨728, c728, 4000, checked728⟩,
  ⟨729, c729, 4000, checked729⟩,
  ⟨730, c730, 4000, checked730⟩,
  ⟨731, c731, 4000, checked731⟩,
  ⟨732, c732, 4000, checked732⟩,
  ⟨733, c733, 4000, checked733⟩,
  ⟨734, c734, 4000, checked734⟩,
  ⟨735, c735, 4000, checked735⟩,
  ⟨736, c736, 4000, checked736⟩,
  ⟨737, c737, 4000, checked737⟩,
  ⟨738, c738, 4000, checked738⟩,
  ⟨739, c739, 4000, checked739⟩,
  ⟨740, c740, 4000, checked740⟩,
  ⟨741, c741, 4000, checked741⟩]

end PA215.ContractShards.Shard005Part5
