import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C037
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard037Part3
open PA215.Contracts PA215.Census

def original4790 : RawOriginal := C037.records[54]'(by decide)
theorem original_id4790 : original4790.index = 4790 := by decide

def c4790 : Contract := original4790.toContract.get (by decide)
theorem binding4790 : original4790.toContract = some c4790 := rfl

theorem checked4790 : check 4000 c4790 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4791 : RawOriginal := C037.records[55]'(by decide)
theorem original_id4791 : original4791.index = 4791 := by decide

def c4791 : Contract := original4791.toContract.get (by decide)
theorem binding4791 : original4791.toContract = some c4791 := rfl

theorem checked4791 : check 4000 c4791 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4792 : RawOriginal := C037.records[56]'(by decide)
theorem original_id4792 : original4792.index = 4792 := by decide

def c4792 : Contract := original4792.toContract.get (by decide)
theorem binding4792 : original4792.toContract = some c4792 := rfl

theorem checked4792 : check 4000 c4792 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4793 : RawOriginal := C037.records[57]'(by decide)
theorem original_id4793 : original4793.index = 4793 := by decide

def c4793 : Contract := original4793.toContract.get (by decide)
theorem binding4793 : original4793.toContract = some c4793 := rfl

theorem checked4793 : check 4000 c4793 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4794 : RawOriginal := C037.records[58]'(by decide)
theorem original_id4794 : original4794.index = 4794 := by decide

def c4794 : Contract := original4794.toContract.get (by decide)
theorem binding4794 : original4794.toContract = some c4794 := rfl

theorem checked4794 : check 4000 c4794 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4795 : RawOriginal := C037.records[59]'(by decide)
theorem original_id4795 : original4795.index = 4795 := by decide

def c4795 : Contract := original4795.toContract.get (by decide)
theorem binding4795 : original4795.toContract = some c4795 := rfl

theorem checked4795 : check 4000 c4795 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4796 : RawOriginal := C037.records[60]'(by decide)
theorem original_id4796 : original4796.index = 4796 := by decide

def c4796 : Contract := original4796.toContract.get (by decide)
theorem binding4796 : original4796.toContract = some c4796 := rfl

theorem checked4796 : check 4000 c4796 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4797 : RawOriginal := C037.records[61]'(by decide)
theorem original_id4797 : original4797.index = 4797 := by decide

def c4797 : Contract := original4797.toContract.get (by decide)
theorem binding4797 : original4797.toContract = some c4797 := rfl

theorem checked4797 : check 4000 c4797 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4798 : RawOriginal := C037.records[62]'(by decide)
theorem original_id4798 : original4798.index = 4798 := by decide

def c4798 : Contract := original4798.toContract.get (by decide)
theorem binding4798 : original4798.toContract = some c4798 := rfl

theorem checked4798 : check 4000 c4798 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4799 : RawOriginal := C037.records[63]'(by decide)
theorem original_id4799 : original4799.index = 4799 := by decide

def c4799 : Contract := original4799.toContract.get (by decide)
theorem binding4799 : original4799.toContract = some c4799 := rfl

theorem checked4799 : check 4000 c4799 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4800 : RawOriginal := C037.records[64]'(by decide)
theorem original_id4800 : original4800.index = 4800 := by decide

def c4800 : Contract := original4800.toContract.get (by decide)
theorem binding4800 : original4800.toContract = some c4800 := rfl

theorem checked4800 : check 4000 c4800 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4801 : RawOriginal := C037.records[65]'(by decide)
theorem original_id4801 : original4801.index = 4801 := by decide

def c4801 : Contract := original4801.toContract.get (by decide)
theorem binding4801 : original4801.toContract = some c4801 := rfl

theorem checked4801 : check 4000 c4801 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4802 : RawOriginal := C037.records[66]'(by decide)
theorem original_id4802 : original4802.index = 4802 := by decide

def c4802 : Contract := original4802.toContract.get (by decide)
theorem binding4802 : original4802.toContract = some c4802 := rfl

theorem checked4802 : check 4000 c4802 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4803 : RawOriginal := C037.records[67]'(by decide)
theorem original_id4803 : original4803.index = 4803 := by decide

def c4803 : Contract := original4803.toContract.get (by decide)
theorem binding4803 : original4803.toContract = some c4803 := rfl

theorem checked4803 : check 4000 c4803 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4804 : RawOriginal := C037.records[68]'(by decide)
theorem original_id4804 : original4804.index = 4804 := by decide

def c4804 : Contract := original4804.toContract.get (by decide)
theorem binding4804 : original4804.toContract = some c4804 := rfl

theorem checked4804 : check 4000 c4804 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4805 : RawOriginal := C037.records[69]'(by decide)
theorem original_id4805 : original4805.index = 4805 := by decide

def c4805 : Contract := original4805.toContract.get (by decide)
theorem binding4805 : original4805.toContract = some c4805 := rfl

theorem checked4805 : check 4000 c4805 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4790, c4790, 4000, checked4790⟩,
  ⟨4791, c4791, 4000, checked4791⟩,
  ⟨4792, c4792, 4000, checked4792⟩,
  ⟨4793, c4793, 4000, checked4793⟩,
  ⟨4794, c4794, 4000, checked4794⟩,
  ⟨4795, c4795, 4000, checked4795⟩,
  ⟨4796, c4796, 4000, checked4796⟩,
  ⟨4797, c4797, 4000, checked4797⟩,
  ⟨4798, c4798, 4000, checked4798⟩,
  ⟨4799, c4799, 4000, checked4799⟩,
  ⟨4800, c4800, 4000, checked4800⟩,
  ⟨4801, c4801, 4000, checked4801⟩,
  ⟨4802, c4802, 4000, checked4802⟩,
  ⟨4803, c4803, 4000, checked4803⟩,
  ⟨4804, c4804, 4000, checked4804⟩,
  ⟨4805, c4805, 4000, checked4805⟩]

end PA215.ContractShards.Shard037Part3
