import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C036
import PA215.Census.C037
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard036Part7
open PA215.Contracts PA215.Census

def original4726 : RawOriginal := C036.records[118]'(by decide)
theorem original_id4726 : original4726.index = 4726 := by decide

def c4726 : Contract := original4726.toContract.get (by decide)
theorem binding4726 : original4726.toContract = some c4726 := rfl

theorem checked4726 : check 4000 c4726 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4727 : RawOriginal := C036.records[119]'(by decide)
theorem original_id4727 : original4727.index = 4727 := by decide

def c4727 : Contract := original4727.toContract.get (by decide)
theorem binding4727 : original4727.toContract = some c4727 := rfl

theorem checked4727 : check 4000 c4727 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4728 : RawOriginal := C036.records[120]'(by decide)
theorem original_id4728 : original4728.index = 4728 := by decide

def c4728 : Contract := original4728.toContract.get (by decide)
theorem binding4728 : original4728.toContract = some c4728 := rfl

theorem checked4728 : check 4000 c4728 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4729 : RawOriginal := C036.records[121]'(by decide)
theorem original_id4729 : original4729.index = 4729 := by decide

def c4729 : Contract := original4729.toContract.get (by decide)
theorem binding4729 : original4729.toContract = some c4729 := rfl

theorem checked4729 : check 4000 c4729 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4730 : RawOriginal := C036.records[122]'(by decide)
theorem original_id4730 : original4730.index = 4730 := by decide

def c4730 : Contract := original4730.toContract.get (by decide)
theorem binding4730 : original4730.toContract = some c4730 := rfl

theorem checked4730 : check 4000 c4730 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4731 : RawOriginal := C036.records[123]'(by decide)
theorem original_id4731 : original4731.index = 4731 := by decide

def c4731 : Contract := original4731.toContract.get (by decide)
theorem binding4731 : original4731.toContract = some c4731 := rfl

theorem checked4731 : check 4000 c4731 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4732 : RawOriginal := C036.records[124]'(by decide)
theorem original_id4732 : original4732.index = 4732 := by decide

def c4732 : Contract := original4732.toContract.get (by decide)
theorem binding4732 : original4732.toContract = some c4732 := rfl

theorem checked4732 : check 4000 c4732 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4733 : RawOriginal := C036.records[125]'(by decide)
theorem original_id4733 : original4733.index = 4733 := by decide

def c4733 : Contract := original4733.toContract.get (by decide)
theorem binding4733 : original4733.toContract = some c4733 := rfl

theorem checked4733 : check 4000 c4733 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4734 : RawOriginal := C036.records[126]'(by decide)
theorem original_id4734 : original4734.index = 4734 := by decide

def c4734 : Contract := original4734.toContract.get (by decide)
theorem binding4734 : original4734.toContract = some c4734 := rfl

theorem checked4734 : check 4000 c4734 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4735 : RawOriginal := C036.records[127]'(by decide)
theorem original_id4735 : original4735.index = 4735 := by decide

def c4735 : Contract := original4735.toContract.get (by decide)
theorem binding4735 : original4735.toContract = some c4735 := rfl

theorem checked4735 : check 4000 c4735 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4736 : RawOriginal := C037.records[0]'(by decide)
theorem original_id4736 : original4736.index = 4736 := by decide

def c4736 : Contract := original4736.toContract.get (by decide)
theorem binding4736 : original4736.toContract = some c4736 := rfl

theorem checked4736 : check 4000 c4736 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4737 : RawOriginal := C037.records[1]'(by decide)
theorem original_id4737 : original4737.index = 4737 := by decide

def c4737 : Contract := original4737.toContract.get (by decide)
theorem binding4737 : original4737.toContract = some c4737 := rfl

theorem checked4737 : check 4000 c4737 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4738 : RawOriginal := C037.records[2]'(by decide)
theorem original_id4738 : original4738.index = 4738 := by decide

def c4738 : Contract := original4738.toContract.get (by decide)
theorem binding4738 : original4738.toContract = some c4738 := rfl

theorem checked4738 : check 4000 c4738 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4739 : RawOriginal := C037.records[3]'(by decide)
theorem original_id4739 : original4739.index = 4739 := by decide

def c4739 : Contract := original4739.toContract.get (by decide)
theorem binding4739 : original4739.toContract = some c4739 := rfl

theorem checked4739 : check 4000 c4739 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4740 : RawOriginal := C037.records[4]'(by decide)
theorem original_id4740 : original4740.index = 4740 := by decide

def c4740 : Contract := original4740.toContract.get (by decide)
theorem binding4740 : original4740.toContract = some c4740 := rfl

theorem checked4740 : check 4000 c4740 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4741 : RawOriginal := C037.records[5]'(by decide)
theorem original_id4741 : original4741.index = 4741 := by decide

def c4741 : Contract := original4741.toContract.get (by decide)
theorem binding4741 : original4741.toContract = some c4741 := rfl

theorem checked4741 : check 4000 c4741 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4726, c4726, 4000, checked4726⟩,
  ⟨4727, c4727, 4000, checked4727⟩,
  ⟨4728, c4728, 4000, checked4728⟩,
  ⟨4729, c4729, 4000, checked4729⟩,
  ⟨4730, c4730, 4000, checked4730⟩,
  ⟨4731, c4731, 4000, checked4731⟩,
  ⟨4732, c4732, 4000, checked4732⟩,
  ⟨4733, c4733, 4000, checked4733⟩,
  ⟨4734, c4734, 4000, checked4734⟩,
  ⟨4735, c4735, 4000, checked4735⟩,
  ⟨4736, c4736, 4000, checked4736⟩,
  ⟨4737, c4737, 4000, checked4737⟩,
  ⟨4738, c4738, 4000, checked4738⟩,
  ⟨4739, c4739, 4000, checked4739⟩,
  ⟨4740, c4740, 4000, checked4740⟩,
  ⟨4741, c4741, 4000, checked4741⟩]

end PA215.ContractShards.Shard036Part7
