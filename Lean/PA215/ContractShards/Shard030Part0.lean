import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C030
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard030Part0
open PA215.Contracts PA215.Census

def original3846 : RawOriginal := C030.records[6]'(by decide)
theorem original_id3846 : original3846.index = 3846 := by decide

def c3846 : Contract := original3846.toContract.get (by decide)
theorem binding3846 : original3846.toContract = some c3846 := rfl

theorem checked3846 : check 4000 c3846 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3847 : RawOriginal := C030.records[7]'(by decide)
theorem original_id3847 : original3847.index = 3847 := by decide

def c3847 : Contract := original3847.toContract.get (by decide)
theorem binding3847 : original3847.toContract = some c3847 := rfl

theorem checked3847 : check 4000 c3847 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3848 : RawOriginal := C030.records[8]'(by decide)
theorem original_id3848 : original3848.index = 3848 := by decide

def c3848 : Contract := original3848.toContract.get (by decide)
theorem binding3848 : original3848.toContract = some c3848 := rfl

theorem checked3848 : check 4000 c3848 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3849 : RawOriginal := C030.records[9]'(by decide)
theorem original_id3849 : original3849.index = 3849 := by decide

def c3849 : Contract := original3849.toContract.get (by decide)
theorem binding3849 : original3849.toContract = some c3849 := rfl

theorem checked3849 : check 4000 c3849 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3850 : RawOriginal := C030.records[10]'(by decide)
theorem original_id3850 : original3850.index = 3850 := by decide

def c3850 : Contract := original3850.toContract.get (by decide)
theorem binding3850 : original3850.toContract = some c3850 := rfl

theorem checked3850 : check 4000 c3850 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3851 : RawOriginal := C030.records[11]'(by decide)
theorem original_id3851 : original3851.index = 3851 := by decide

def c3851 : Contract := original3851.toContract.get (by decide)
theorem binding3851 : original3851.toContract = some c3851 := rfl

theorem checked3851 : check 4000 c3851 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3852 : RawOriginal := C030.records[12]'(by decide)
theorem original_id3852 : original3852.index = 3852 := by decide

def c3852 : Contract := original3852.toContract.get (by decide)
theorem binding3852 : original3852.toContract = some c3852 := rfl

theorem checked3852 : check 4000 c3852 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3853 : RawOriginal := C030.records[13]'(by decide)
theorem original_id3853 : original3853.index = 3853 := by decide

def c3853 : Contract := original3853.toContract.get (by decide)
theorem binding3853 : original3853.toContract = some c3853 := rfl

theorem checked3853 : check 4000 c3853 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3854 : RawOriginal := C030.records[14]'(by decide)
theorem original_id3854 : original3854.index = 3854 := by decide

def c3854 : Contract := original3854.toContract.get (by decide)
theorem binding3854 : original3854.toContract = some c3854 := rfl

theorem checked3854 : check 4000 c3854 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3855 : RawOriginal := C030.records[15]'(by decide)
theorem original_id3855 : original3855.index = 3855 := by decide

def c3855 : Contract := original3855.toContract.get (by decide)
theorem binding3855 : original3855.toContract = some c3855 := rfl

theorem checked3855 : check 4000 c3855 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3856 : RawOriginal := C030.records[16]'(by decide)
theorem original_id3856 : original3856.index = 3856 := by decide

def c3856 : Contract := original3856.toContract.get (by decide)
theorem binding3856 : original3856.toContract = some c3856 := rfl

theorem checked3856 : check 4000 c3856 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3857 : RawOriginal := C030.records[17]'(by decide)
theorem original_id3857 : original3857.index = 3857 := by decide

def c3857 : Contract := original3857.toContract.get (by decide)
theorem binding3857 : original3857.toContract = some c3857 := rfl

theorem checked3857 : check 4000 c3857 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3858 : RawOriginal := C030.records[18]'(by decide)
theorem original_id3858 : original3858.index = 3858 := by decide

def c3858 : Contract := original3858.toContract.get (by decide)
theorem binding3858 : original3858.toContract = some c3858 := rfl

theorem checked3858 : check 4000 c3858 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3859 : RawOriginal := C030.records[19]'(by decide)
theorem original_id3859 : original3859.index = 3859 := by decide

def c3859 : Contract := original3859.toContract.get (by decide)
theorem binding3859 : original3859.toContract = some c3859 := rfl

theorem checked3859 : check 4000 c3859 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3860 : RawOriginal := C030.records[20]'(by decide)
theorem original_id3860 : original3860.index = 3860 := by decide

def c3860 : Contract := original3860.toContract.get (by decide)
theorem binding3860 : original3860.toContract = some c3860 := rfl

theorem checked3860 : check 4000 c3860 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3861 : RawOriginal := C030.records[21]'(by decide)
theorem original_id3861 : original3861.index = 3861 := by decide

def c3861 : Contract := original3861.toContract.get (by decide)
theorem binding3861 : original3861.toContract = some c3861 := rfl

theorem checked3861 : check 4000 c3861 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3846, c3846, 4000, checked3846⟩,
  ⟨3847, c3847, 4000, checked3847⟩,
  ⟨3848, c3848, 4000, checked3848⟩,
  ⟨3849, c3849, 4000, checked3849⟩,
  ⟨3850, c3850, 4000, checked3850⟩,
  ⟨3851, c3851, 4000, checked3851⟩,
  ⟨3852, c3852, 4000, checked3852⟩,
  ⟨3853, c3853, 4000, checked3853⟩,
  ⟨3854, c3854, 4000, checked3854⟩,
  ⟨3855, c3855, 4000, checked3855⟩,
  ⟨3856, c3856, 4000, checked3856⟩,
  ⟨3857, c3857, 4000, checked3857⟩,
  ⟨3858, c3858, 4000, checked3858⟩,
  ⟨3859, c3859, 4000, checked3859⟩,
  ⟨3860, c3860, 4000, checked3860⟩,
  ⟨3861, c3861, 4000, checked3861⟩]

end PA215.ContractShards.Shard030Part0
