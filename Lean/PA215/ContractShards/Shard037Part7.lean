import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C037
import PA215.Census.C038
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard037Part7
open PA215.Contracts PA215.Census

def original4854 : RawOriginal := C037.records[118]'(by decide)
theorem original_id4854 : original4854.index = 4854 := by decide

def c4854 : Contract := original4854.toContract.get (by decide)
theorem binding4854 : original4854.toContract = some c4854 := rfl

theorem checked4854 : check 4000 c4854 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4855 : RawOriginal := C037.records[119]'(by decide)
theorem original_id4855 : original4855.index = 4855 := by decide

def c4855 : Contract := original4855.toContract.get (by decide)
theorem binding4855 : original4855.toContract = some c4855 := rfl

theorem checked4855 : check 4000 c4855 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4856 : RawOriginal := C037.records[120]'(by decide)
theorem original_id4856 : original4856.index = 4856 := by decide

def c4856 : Contract := original4856.toContract.get (by decide)
theorem binding4856 : original4856.toContract = some c4856 := rfl

theorem checked4856 : check 4000 c4856 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4857 : RawOriginal := C037.records[121]'(by decide)
theorem original_id4857 : original4857.index = 4857 := by decide

def c4857 : Contract := original4857.toContract.get (by decide)
theorem binding4857 : original4857.toContract = some c4857 := rfl

theorem checked4857 : check 4000 c4857 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4858 : RawOriginal := C037.records[122]'(by decide)
theorem original_id4858 : original4858.index = 4858 := by decide

def c4858 : Contract := original4858.toContract.get (by decide)
theorem binding4858 : original4858.toContract = some c4858 := rfl

theorem checked4858 : check 4000 c4858 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4859 : RawOriginal := C037.records[123]'(by decide)
theorem original_id4859 : original4859.index = 4859 := by decide

def c4859 : Contract := original4859.toContract.get (by decide)
theorem binding4859 : original4859.toContract = some c4859 := rfl

theorem checked4859 : check 4000 c4859 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4860 : RawOriginal := C037.records[124]'(by decide)
theorem original_id4860 : original4860.index = 4860 := by decide

def c4860 : Contract := original4860.toContract.get (by decide)
theorem binding4860 : original4860.toContract = some c4860 := rfl

theorem checked4860 : check 4000 c4860 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4861 : RawOriginal := C037.records[125]'(by decide)
theorem original_id4861 : original4861.index = 4861 := by decide

def c4861 : Contract := original4861.toContract.get (by decide)
theorem binding4861 : original4861.toContract = some c4861 := rfl

theorem checked4861 : check 4000 c4861 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4862 : RawOriginal := C037.records[126]'(by decide)
theorem original_id4862 : original4862.index = 4862 := by decide

def c4862 : Contract := original4862.toContract.get (by decide)
theorem binding4862 : original4862.toContract = some c4862 := rfl

theorem checked4862 : check 4000 c4862 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4863 : RawOriginal := C037.records[127]'(by decide)
theorem original_id4863 : original4863.index = 4863 := by decide

def c4863 : Contract := original4863.toContract.get (by decide)
theorem binding4863 : original4863.toContract = some c4863 := rfl

theorem checked4863 : check 4000 c4863 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4864 : RawOriginal := C038.records[0]'(by decide)
theorem original_id4864 : original4864.index = 4864 := by decide

def c4864 : Contract := original4864.toContract.get (by decide)
theorem binding4864 : original4864.toContract = some c4864 := rfl

theorem checked4864 : check 4000 c4864 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4865 : RawOriginal := C038.records[1]'(by decide)
theorem original_id4865 : original4865.index = 4865 := by decide

def c4865 : Contract := original4865.toContract.get (by decide)
theorem binding4865 : original4865.toContract = some c4865 := rfl

theorem checked4865 : check 4000 c4865 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4866 : RawOriginal := C038.records[2]'(by decide)
theorem original_id4866 : original4866.index = 4866 := by decide

def c4866 : Contract := original4866.toContract.get (by decide)
theorem binding4866 : original4866.toContract = some c4866 := rfl

theorem checked4866 : check 4000 c4866 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4867 : RawOriginal := C038.records[3]'(by decide)
theorem original_id4867 : original4867.index = 4867 := by decide

def c4867 : Contract := original4867.toContract.get (by decide)
theorem binding4867 : original4867.toContract = some c4867 := rfl

theorem checked4867 : check 4000 c4867 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4868 : RawOriginal := C038.records[4]'(by decide)
theorem original_id4868 : original4868.index = 4868 := by decide

def c4868 : Contract := original4868.toContract.get (by decide)
theorem binding4868 : original4868.toContract = some c4868 := rfl

theorem checked4868 : check 4000 c4868 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4869 : RawOriginal := C038.records[5]'(by decide)
theorem original_id4869 : original4869.index = 4869 := by decide

def c4869 : Contract := original4869.toContract.get (by decide)
theorem binding4869 : original4869.toContract = some c4869 := rfl

theorem checked4869 : check 4000 c4869 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4854, c4854, 4000, checked4854⟩,
  ⟨4855, c4855, 4000, checked4855⟩,
  ⟨4856, c4856, 4000, checked4856⟩,
  ⟨4857, c4857, 4000, checked4857⟩,
  ⟨4858, c4858, 4000, checked4858⟩,
  ⟨4859, c4859, 4000, checked4859⟩,
  ⟨4860, c4860, 4000, checked4860⟩,
  ⟨4861, c4861, 4000, checked4861⟩,
  ⟨4862, c4862, 4000, checked4862⟩,
  ⟨4863, c4863, 4000, checked4863⟩,
  ⟨4864, c4864, 4000, checked4864⟩,
  ⟨4865, c4865, 4000, checked4865⟩,
  ⟨4866, c4866, 4000, checked4866⟩,
  ⟨4867, c4867, 4000, checked4867⟩,
  ⟨4868, c4868, 4000, checked4868⟩,
  ⟨4869, c4869, 4000, checked4869⟩]

end PA215.ContractShards.Shard037Part7
