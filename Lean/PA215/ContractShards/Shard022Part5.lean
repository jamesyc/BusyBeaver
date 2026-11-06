import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C022
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard022Part5
open PA215.Contracts PA215.Census

def original2902 : RawOriginal := C022.records[86]'(by decide)
theorem original_id2902 : original2902.index = 2902 := by decide

def c2902 : Contract := original2902.toContract.get (by decide)
theorem binding2902 : original2902.toContract = some c2902 := rfl

theorem checked2902 : check 4000 c2902 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2903 : RawOriginal := C022.records[87]'(by decide)
theorem original_id2903 : original2903.index = 2903 := by decide

def c2903 : Contract := original2903.toContract.get (by decide)
theorem binding2903 : original2903.toContract = some c2903 := rfl

theorem checked2903 : check 4000 c2903 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2904 : RawOriginal := C022.records[88]'(by decide)
theorem original_id2904 : original2904.index = 2904 := by decide

def c2904 : Contract := original2904.toContract.get (by decide)
theorem binding2904 : original2904.toContract = some c2904 := rfl

theorem checked2904 : check 4000 c2904 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2905 : RawOriginal := C022.records[89]'(by decide)
theorem original_id2905 : original2905.index = 2905 := by decide

def c2905 : Contract := original2905.toContract.get (by decide)
theorem binding2905 : original2905.toContract = some c2905 := rfl

theorem checked2905 : check 4000 c2905 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2906 : RawOriginal := C022.records[90]'(by decide)
theorem original_id2906 : original2906.index = 2906 := by decide

def c2906 : Contract := original2906.toContract.get (by decide)
theorem binding2906 : original2906.toContract = some c2906 := rfl

theorem checked2906 : check 4000 c2906 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2907 : RawOriginal := C022.records[91]'(by decide)
theorem original_id2907 : original2907.index = 2907 := by decide

def c2907 : Contract := original2907.toContract.get (by decide)
theorem binding2907 : original2907.toContract = some c2907 := rfl

theorem checked2907 : check 4000 c2907 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2908 : RawOriginal := C022.records[92]'(by decide)
theorem original_id2908 : original2908.index = 2908 := by decide

def c2908 : Contract := original2908.toContract.get (by decide)
theorem binding2908 : original2908.toContract = some c2908 := rfl

theorem checked2908 : check 4000 c2908 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2909 : RawOriginal := C022.records[93]'(by decide)
theorem original_id2909 : original2909.index = 2909 := by decide

def c2909 : Contract := original2909.toContract.get (by decide)
theorem binding2909 : original2909.toContract = some c2909 := rfl

theorem checked2909 : check 4000 c2909 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2910 : RawOriginal := C022.records[94]'(by decide)
theorem original_id2910 : original2910.index = 2910 := by decide

def c2910 : Contract := original2910.toContract.get (by decide)
theorem binding2910 : original2910.toContract = some c2910 := rfl

theorem checked2910 : check 4000 c2910 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2911 : RawOriginal := C022.records[95]'(by decide)
theorem original_id2911 : original2911.index = 2911 := by decide

def c2911 : Contract := original2911.toContract.get (by decide)
theorem binding2911 : original2911.toContract = some c2911 := rfl

theorem checked2911 : check 4000 c2911 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2912 : RawOriginal := C022.records[96]'(by decide)
theorem original_id2912 : original2912.index = 2912 := by decide

def c2912 : Contract := original2912.toContract.get (by decide)
theorem binding2912 : original2912.toContract = some c2912 := rfl

theorem checked2912 : check 4000 c2912 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2913 : RawOriginal := C022.records[97]'(by decide)
theorem original_id2913 : original2913.index = 2913 := by decide

def c2913 : Contract := original2913.toContract.get (by decide)
theorem binding2913 : original2913.toContract = some c2913 := rfl

theorem checked2913 : check 4000 c2913 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2914 : RawOriginal := C022.records[98]'(by decide)
theorem original_id2914 : original2914.index = 2914 := by decide

def c2914 : Contract := original2914.toContract.get (by decide)
theorem binding2914 : original2914.toContract = some c2914 := rfl

theorem checked2914 : check 4000 c2914 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2915 : RawOriginal := C022.records[99]'(by decide)
theorem original_id2915 : original2915.index = 2915 := by decide

def c2915 : Contract := original2915.toContract.get (by decide)
theorem binding2915 : original2915.toContract = some c2915 := rfl

theorem checked2915 : check 4000 c2915 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2916 : RawOriginal := C022.records[100]'(by decide)
theorem original_id2916 : original2916.index = 2916 := by decide

def c2916 : Contract := original2916.toContract.get (by decide)
theorem binding2916 : original2916.toContract = some c2916 := rfl

theorem checked2916 : check 4000 c2916 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2917 : RawOriginal := C022.records[101]'(by decide)
theorem original_id2917 : original2917.index = 2917 := by decide

def c2917 : Contract := original2917.toContract.get (by decide)
theorem binding2917 : original2917.toContract = some c2917 := rfl

theorem checked2917 : check 4000 c2917 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2902, c2902, 4000, checked2902⟩,
  ⟨2903, c2903, 4000, checked2903⟩,
  ⟨2904, c2904, 4000, checked2904⟩,
  ⟨2905, c2905, 4000, checked2905⟩,
  ⟨2906, c2906, 4000, checked2906⟩,
  ⟨2907, c2907, 4000, checked2907⟩,
  ⟨2908, c2908, 4000, checked2908⟩,
  ⟨2909, c2909, 4000, checked2909⟩,
  ⟨2910, c2910, 4000, checked2910⟩,
  ⟨2911, c2911, 4000, checked2911⟩,
  ⟨2912, c2912, 4000, checked2912⟩,
  ⟨2913, c2913, 4000, checked2913⟩,
  ⟨2914, c2914, 4000, checked2914⟩,
  ⟨2915, c2915, 4000, checked2915⟩,
  ⟨2916, c2916, 4000, checked2916⟩,
  ⟨2917, c2917, 4000, checked2917⟩]

end PA215.ContractShards.Shard022Part5
