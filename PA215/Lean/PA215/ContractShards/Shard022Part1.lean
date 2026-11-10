import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C022
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard022Part1
open PA215.Contracts PA215.Census

def original2838 : RawOriginal := C022.records[22]'(by decide)
theorem original_id2838 : original2838.index = 2838 := by decide

def c2838 : Contract := original2838.toContract.get (by decide)
theorem binding2838 : original2838.toContract = some c2838 := rfl

theorem checked2838 : check 4000 c2838 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2839 : RawOriginal := C022.records[23]'(by decide)
theorem original_id2839 : original2839.index = 2839 := by decide

def c2839 : Contract := original2839.toContract.get (by decide)
theorem binding2839 : original2839.toContract = some c2839 := rfl

theorem checked2839 : check 4000 c2839 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2840 : RawOriginal := C022.records[24]'(by decide)
theorem original_id2840 : original2840.index = 2840 := by decide

def c2840 : Contract := original2840.toContract.get (by decide)
theorem binding2840 : original2840.toContract = some c2840 := rfl

theorem checked2840 : check 4000 c2840 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2841 : RawOriginal := C022.records[25]'(by decide)
theorem original_id2841 : original2841.index = 2841 := by decide

def c2841 : Contract := original2841.toContract.get (by decide)
theorem binding2841 : original2841.toContract = some c2841 := rfl

theorem checked2841 : check 4000 c2841 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2842 : RawOriginal := C022.records[26]'(by decide)
theorem original_id2842 : original2842.index = 2842 := by decide

def c2842 : Contract := original2842.toContract.get (by decide)
theorem binding2842 : original2842.toContract = some c2842 := rfl

theorem checked2842 : check 4000 c2842 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2843 : RawOriginal := C022.records[27]'(by decide)
theorem original_id2843 : original2843.index = 2843 := by decide

def c2843 : Contract := original2843.toContract.get (by decide)
theorem binding2843 : original2843.toContract = some c2843 := rfl

theorem checked2843 : check 4000 c2843 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2844 : RawOriginal := C022.records[28]'(by decide)
theorem original_id2844 : original2844.index = 2844 := by decide

def c2844 : Contract := original2844.toContract.get (by decide)
theorem binding2844 : original2844.toContract = some c2844 := rfl

theorem checked2844 : check 4000 c2844 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2845 : RawOriginal := C022.records[29]'(by decide)
theorem original_id2845 : original2845.index = 2845 := by decide

def c2845 : Contract := original2845.toContract.get (by decide)
theorem binding2845 : original2845.toContract = some c2845 := rfl

theorem checked2845 : check 4000 c2845 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2846 : RawOriginal := C022.records[30]'(by decide)
theorem original_id2846 : original2846.index = 2846 := by decide

def c2846 : Contract := original2846.toContract.get (by decide)
theorem binding2846 : original2846.toContract = some c2846 := rfl

theorem checked2846 : check 4000 c2846 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2847 : RawOriginal := C022.records[31]'(by decide)
theorem original_id2847 : original2847.index = 2847 := by decide

def c2847 : Contract := original2847.toContract.get (by decide)
theorem binding2847 : original2847.toContract = some c2847 := rfl

theorem checked2847 : check 4000 c2847 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2848 : RawOriginal := C022.records[32]'(by decide)
theorem original_id2848 : original2848.index = 2848 := by decide

def c2848 : Contract := original2848.toContract.get (by decide)
theorem binding2848 : original2848.toContract = some c2848 := rfl

theorem checked2848 : check 4000 c2848 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2849 : RawOriginal := C022.records[33]'(by decide)
theorem original_id2849 : original2849.index = 2849 := by decide

def c2849 : Contract := original2849.toContract.get (by decide)
theorem binding2849 : original2849.toContract = some c2849 := rfl

theorem checked2849 : check 4000 c2849 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2850 : RawOriginal := C022.records[34]'(by decide)
theorem original_id2850 : original2850.index = 2850 := by decide

def c2850 : Contract := original2850.toContract.get (by decide)
theorem binding2850 : original2850.toContract = some c2850 := rfl

theorem checked2850 : check 4000 c2850 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2851 : RawOriginal := C022.records[35]'(by decide)
theorem original_id2851 : original2851.index = 2851 := by decide

def c2851 : Contract := original2851.toContract.get (by decide)
theorem binding2851 : original2851.toContract = some c2851 := rfl

theorem checked2851 : check 4000 c2851 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2852 : RawOriginal := C022.records[36]'(by decide)
theorem original_id2852 : original2852.index = 2852 := by decide

def c2852 : Contract := original2852.toContract.get (by decide)
theorem binding2852 : original2852.toContract = some c2852 := rfl

theorem checked2852 : check 4000 c2852 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2853 : RawOriginal := C022.records[37]'(by decide)
theorem original_id2853 : original2853.index = 2853 := by decide

def c2853 : Contract := original2853.toContract.get (by decide)
theorem binding2853 : original2853.toContract = some c2853 := rfl

theorem checked2853 : check 4000 c2853 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2838, c2838, 4000, checked2838⟩,
  ⟨2839, c2839, 4000, checked2839⟩,
  ⟨2840, c2840, 4000, checked2840⟩,
  ⟨2841, c2841, 4000, checked2841⟩,
  ⟨2842, c2842, 4000, checked2842⟩,
  ⟨2843, c2843, 4000, checked2843⟩,
  ⟨2844, c2844, 4000, checked2844⟩,
  ⟨2845, c2845, 4000, checked2845⟩,
  ⟨2846, c2846, 4000, checked2846⟩,
  ⟨2847, c2847, 4000, checked2847⟩,
  ⟨2848, c2848, 4000, checked2848⟩,
  ⟨2849, c2849, 4000, checked2849⟩,
  ⟨2850, c2850, 4000, checked2850⟩,
  ⟨2851, c2851, 4000, checked2851⟩,
  ⟨2852, c2852, 4000, checked2852⟩,
  ⟨2853, c2853, 4000, checked2853⟩]

end PA215.ContractShards.Shard022Part1
