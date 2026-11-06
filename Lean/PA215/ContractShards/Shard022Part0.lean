import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C022
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard022Part0
open PA215.Contracts PA215.Census

def original2822 : RawOriginal := C022.records[6]'(by decide)
theorem original_id2822 : original2822.index = 2822 := by decide

def c2822 : Contract := original2822.toContract.get (by decide)
theorem binding2822 : original2822.toContract = some c2822 := rfl

theorem checked2822 : check 4000 c2822 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2823 : RawOriginal := C022.records[7]'(by decide)
theorem original_id2823 : original2823.index = 2823 := by decide

def c2823 : Contract := original2823.toContract.get (by decide)
theorem binding2823 : original2823.toContract = some c2823 := rfl

theorem checked2823 : check 4000 c2823 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2824 : RawOriginal := C022.records[8]'(by decide)
theorem original_id2824 : original2824.index = 2824 := by decide

def c2824 : Contract := original2824.toContract.get (by decide)
theorem binding2824 : original2824.toContract = some c2824 := rfl

theorem checked2824 : check 4000 c2824 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2825 : RawOriginal := C022.records[9]'(by decide)
theorem original_id2825 : original2825.index = 2825 := by decide

def c2825 : Contract := original2825.toContract.get (by decide)
theorem binding2825 : original2825.toContract = some c2825 := rfl

theorem checked2825 : check 4000 c2825 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2826 : RawOriginal := C022.records[10]'(by decide)
theorem original_id2826 : original2826.index = 2826 := by decide

def c2826 : Contract := original2826.toContract.get (by decide)
theorem binding2826 : original2826.toContract = some c2826 := rfl

theorem checked2826 : check 4000 c2826 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2827 : RawOriginal := C022.records[11]'(by decide)
theorem original_id2827 : original2827.index = 2827 := by decide

def c2827 : Contract := original2827.toContract.get (by decide)
theorem binding2827 : original2827.toContract = some c2827 := rfl

theorem checked2827 : check 4000 c2827 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2828 : RawOriginal := C022.records[12]'(by decide)
theorem original_id2828 : original2828.index = 2828 := by decide

def c2828 : Contract := original2828.toContract.get (by decide)
theorem binding2828 : original2828.toContract = some c2828 := rfl

theorem checked2828 : check 4000 c2828 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2829 : RawOriginal := C022.records[13]'(by decide)
theorem original_id2829 : original2829.index = 2829 := by decide

def c2829 : Contract := original2829.toContract.get (by decide)
theorem binding2829 : original2829.toContract = some c2829 := rfl

theorem checked2829 : check 4000 c2829 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2830 : RawOriginal := C022.records[14]'(by decide)
theorem original_id2830 : original2830.index = 2830 := by decide

def c2830 : Contract := original2830.toContract.get (by decide)
theorem binding2830 : original2830.toContract = some c2830 := rfl

theorem checked2830 : check 4000 c2830 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2831 : RawOriginal := C022.records[15]'(by decide)
theorem original_id2831 : original2831.index = 2831 := by decide

def c2831 : Contract := original2831.toContract.get (by decide)
theorem binding2831 : original2831.toContract = some c2831 := rfl

theorem checked2831 : check 4000 c2831 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2832 : RawOriginal := C022.records[16]'(by decide)
theorem original_id2832 : original2832.index = 2832 := by decide

def c2832 : Contract := original2832.toContract.get (by decide)
theorem binding2832 : original2832.toContract = some c2832 := rfl

theorem checked2832 : check 4000 c2832 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2833 : RawOriginal := C022.records[17]'(by decide)
theorem original_id2833 : original2833.index = 2833 := by decide

def c2833 : Contract := original2833.toContract.get (by decide)
theorem binding2833 : original2833.toContract = some c2833 := rfl

theorem checked2833 : check 4000 c2833 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2834 : RawOriginal := C022.records[18]'(by decide)
theorem original_id2834 : original2834.index = 2834 := by decide

def c2834 : Contract := original2834.toContract.get (by decide)
theorem binding2834 : original2834.toContract = some c2834 := rfl

theorem checked2834 : check 4000 c2834 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2835 : RawOriginal := C022.records[19]'(by decide)
theorem original_id2835 : original2835.index = 2835 := by decide

def c2835 : Contract := original2835.toContract.get (by decide)
theorem binding2835 : original2835.toContract = some c2835 := rfl

theorem checked2835 : check 4000 c2835 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2836 : RawOriginal := C022.records[20]'(by decide)
theorem original_id2836 : original2836.index = 2836 := by decide

def c2836 : Contract := original2836.toContract.get (by decide)
theorem binding2836 : original2836.toContract = some c2836 := rfl

theorem checked2836 : check 4000 c2836 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2837 : RawOriginal := C022.records[21]'(by decide)
theorem original_id2837 : original2837.index = 2837 := by decide

def c2837 : Contract := original2837.toContract.get (by decide)
theorem binding2837 : original2837.toContract = some c2837 := rfl

theorem checked2837 : check 4000 c2837 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2822, c2822, 4000, checked2822⟩,
  ⟨2823, c2823, 4000, checked2823⟩,
  ⟨2824, c2824, 4000, checked2824⟩,
  ⟨2825, c2825, 4000, checked2825⟩,
  ⟨2826, c2826, 4000, checked2826⟩,
  ⟨2827, c2827, 4000, checked2827⟩,
  ⟨2828, c2828, 4000, checked2828⟩,
  ⟨2829, c2829, 4000, checked2829⟩,
  ⟨2830, c2830, 4000, checked2830⟩,
  ⟨2831, c2831, 4000, checked2831⟩,
  ⟨2832, c2832, 4000, checked2832⟩,
  ⟨2833, c2833, 4000, checked2833⟩,
  ⟨2834, c2834, 4000, checked2834⟩,
  ⟨2835, c2835, 4000, checked2835⟩,
  ⟨2836, c2836, 4000, checked2836⟩,
  ⟨2837, c2837, 4000, checked2837⟩]

end PA215.ContractShards.Shard022Part0
