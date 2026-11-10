import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C022
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard022Part3
open PA215.Contracts PA215.Census

def original2870 : RawOriginal := C022.records[54]'(by decide)
theorem original_id2870 : original2870.index = 2870 := by decide

def c2870 : Contract := original2870.toContract.get (by decide)
theorem binding2870 : original2870.toContract = some c2870 := rfl

theorem checked2870 : check 4000 c2870 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2871 : RawOriginal := C022.records[55]'(by decide)
theorem original_id2871 : original2871.index = 2871 := by decide

def c2871 : Contract := original2871.toContract.get (by decide)
theorem binding2871 : original2871.toContract = some c2871 := rfl

theorem checked2871 : check 4000 c2871 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2872 : RawOriginal := C022.records[56]'(by decide)
theorem original_id2872 : original2872.index = 2872 := by decide

def c2872 : Contract := original2872.toContract.get (by decide)
theorem binding2872 : original2872.toContract = some c2872 := rfl

theorem checked2872 : check 4000 c2872 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2873 : RawOriginal := C022.records[57]'(by decide)
theorem original_id2873 : original2873.index = 2873 := by decide

def c2873 : Contract := original2873.toContract.get (by decide)
theorem binding2873 : original2873.toContract = some c2873 := rfl

theorem checked2873 : check 4000 c2873 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2874 : RawOriginal := C022.records[58]'(by decide)
theorem original_id2874 : original2874.index = 2874 := by decide

def c2874 : Contract := original2874.toContract.get (by decide)
theorem binding2874 : original2874.toContract = some c2874 := rfl

theorem checked2874 : check 4000 c2874 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2875 : RawOriginal := C022.records[59]'(by decide)
theorem original_id2875 : original2875.index = 2875 := by decide

def c2875 : Contract := original2875.toContract.get (by decide)
theorem binding2875 : original2875.toContract = some c2875 := rfl

theorem checked2875 : check 4000 c2875 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2876 : RawOriginal := C022.records[60]'(by decide)
theorem original_id2876 : original2876.index = 2876 := by decide

def c2876 : Contract := original2876.toContract.get (by decide)
theorem binding2876 : original2876.toContract = some c2876 := rfl

theorem checked2876 : check 4000 c2876 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2877 : RawOriginal := C022.records[61]'(by decide)
theorem original_id2877 : original2877.index = 2877 := by decide

def c2877 : Contract := original2877.toContract.get (by decide)
theorem binding2877 : original2877.toContract = some c2877 := rfl

theorem checked2877 : check 4000 c2877 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2878 : RawOriginal := C022.records[62]'(by decide)
theorem original_id2878 : original2878.index = 2878 := by decide

def c2878 : Contract := original2878.toContract.get (by decide)
theorem binding2878 : original2878.toContract = some c2878 := rfl

theorem checked2878 : check 4000 c2878 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2879 : RawOriginal := C022.records[63]'(by decide)
theorem original_id2879 : original2879.index = 2879 := by decide

def c2879 : Contract := original2879.toContract.get (by decide)
theorem binding2879 : original2879.toContract = some c2879 := rfl

theorem checked2879 : check 4000 c2879 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2880 : RawOriginal := C022.records[64]'(by decide)
theorem original_id2880 : original2880.index = 2880 := by decide

def c2880 : Contract := original2880.toContract.get (by decide)
theorem binding2880 : original2880.toContract = some c2880 := rfl

theorem checked2880 : check 4000 c2880 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2881 : RawOriginal := C022.records[65]'(by decide)
theorem original_id2881 : original2881.index = 2881 := by decide

def c2881 : Contract := original2881.toContract.get (by decide)
theorem binding2881 : original2881.toContract = some c2881 := rfl

theorem checked2881 : check 4000 c2881 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2882 : RawOriginal := C022.records[66]'(by decide)
theorem original_id2882 : original2882.index = 2882 := by decide

def c2882 : Contract := original2882.toContract.get (by decide)
theorem binding2882 : original2882.toContract = some c2882 := rfl

theorem checked2882 : check 4000 c2882 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2883 : RawOriginal := C022.records[67]'(by decide)
theorem original_id2883 : original2883.index = 2883 := by decide

def c2883 : Contract := original2883.toContract.get (by decide)
theorem binding2883 : original2883.toContract = some c2883 := rfl

theorem checked2883 : check 4000 c2883 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2884 : RawOriginal := C022.records[68]'(by decide)
theorem original_id2884 : original2884.index = 2884 := by decide

def c2884 : Contract := original2884.toContract.get (by decide)
theorem binding2884 : original2884.toContract = some c2884 := rfl

theorem checked2884 : check 4000 c2884 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2885 : RawOriginal := C022.records[69]'(by decide)
theorem original_id2885 : original2885.index = 2885 := by decide

def c2885 : Contract := original2885.toContract.get (by decide)
theorem binding2885 : original2885.toContract = some c2885 := rfl

theorem checked2885 : check 4000 c2885 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2870, c2870, 4000, checked2870⟩,
  ⟨2871, c2871, 4000, checked2871⟩,
  ⟨2872, c2872, 4000, checked2872⟩,
  ⟨2873, c2873, 4000, checked2873⟩,
  ⟨2874, c2874, 4000, checked2874⟩,
  ⟨2875, c2875, 4000, checked2875⟩,
  ⟨2876, c2876, 4000, checked2876⟩,
  ⟨2877, c2877, 4000, checked2877⟩,
  ⟨2878, c2878, 4000, checked2878⟩,
  ⟨2879, c2879, 4000, checked2879⟩,
  ⟨2880, c2880, 4000, checked2880⟩,
  ⟨2881, c2881, 4000, checked2881⟩,
  ⟨2882, c2882, 4000, checked2882⟩,
  ⟨2883, c2883, 4000, checked2883⟩,
  ⟨2884, c2884, 4000, checked2884⟩,
  ⟨2885, c2885, 4000, checked2885⟩]

end PA215.ContractShards.Shard022Part3
