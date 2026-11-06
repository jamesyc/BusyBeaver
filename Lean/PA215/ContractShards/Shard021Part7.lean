import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C021
import PA215.Census.C022
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard021Part7
open PA215.Contracts PA215.Census

def original2806 : RawOriginal := C021.records[118]'(by decide)
theorem original_id2806 : original2806.index = 2806 := by decide

def c2806 : Contract := original2806.toContract.get (by decide)
theorem binding2806 : original2806.toContract = some c2806 := rfl

theorem checked2806 : check 4000 c2806 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2807 : RawOriginal := C021.records[119]'(by decide)
theorem original_id2807 : original2807.index = 2807 := by decide

def c2807 : Contract := original2807.toContract.get (by decide)
theorem binding2807 : original2807.toContract = some c2807 := rfl

theorem checked2807 : check 4000 c2807 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2808 : RawOriginal := C021.records[120]'(by decide)
theorem original_id2808 : original2808.index = 2808 := by decide

def c2808 : Contract := original2808.toContract.get (by decide)
theorem binding2808 : original2808.toContract = some c2808 := rfl

theorem checked2808 : check 4000 c2808 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2809 : RawOriginal := C021.records[121]'(by decide)
theorem original_id2809 : original2809.index = 2809 := by decide

def c2809 : Contract := original2809.toContract.get (by decide)
theorem binding2809 : original2809.toContract = some c2809 := rfl

theorem checked2809 : check 4000 c2809 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2810 : RawOriginal := C021.records[122]'(by decide)
theorem original_id2810 : original2810.index = 2810 := by decide

def c2810 : Contract := original2810.toContract.get (by decide)
theorem binding2810 : original2810.toContract = some c2810 := rfl

theorem checked2810 : check 4000 c2810 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2811 : RawOriginal := C021.records[123]'(by decide)
theorem original_id2811 : original2811.index = 2811 := by decide

def c2811 : Contract := original2811.toContract.get (by decide)
theorem binding2811 : original2811.toContract = some c2811 := rfl

theorem checked2811 : check 4000 c2811 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2812 : RawOriginal := C021.records[124]'(by decide)
theorem original_id2812 : original2812.index = 2812 := by decide

def c2812 : Contract := original2812.toContract.get (by decide)
theorem binding2812 : original2812.toContract = some c2812 := rfl

theorem checked2812 : check 4000 c2812 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2813 : RawOriginal := C021.records[125]'(by decide)
theorem original_id2813 : original2813.index = 2813 := by decide

def c2813 : Contract := original2813.toContract.get (by decide)
theorem binding2813 : original2813.toContract = some c2813 := rfl

theorem checked2813 : check 4000 c2813 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2814 : RawOriginal := C021.records[126]'(by decide)
theorem original_id2814 : original2814.index = 2814 := by decide

def c2814 : Contract := original2814.toContract.get (by decide)
theorem binding2814 : original2814.toContract = some c2814 := rfl

theorem checked2814 : check 4000 c2814 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2815 : RawOriginal := C021.records[127]'(by decide)
theorem original_id2815 : original2815.index = 2815 := by decide

def c2815 : Contract := original2815.toContract.get (by decide)
theorem binding2815 : original2815.toContract = some c2815 := rfl

theorem checked2815 : check 4000 c2815 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2816 : RawOriginal := C022.records[0]'(by decide)
theorem original_id2816 : original2816.index = 2816 := by decide

def c2816 : Contract := original2816.toContract.get (by decide)
theorem binding2816 : original2816.toContract = some c2816 := rfl

theorem checked2816 : check 4000 c2816 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2817 : RawOriginal := C022.records[1]'(by decide)
theorem original_id2817 : original2817.index = 2817 := by decide

def c2817 : Contract := original2817.toContract.get (by decide)
theorem binding2817 : original2817.toContract = some c2817 := rfl

theorem checked2817 : check 4000 c2817 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2818 : RawOriginal := C022.records[2]'(by decide)
theorem original_id2818 : original2818.index = 2818 := by decide

def c2818 : Contract := original2818.toContract.get (by decide)
theorem binding2818 : original2818.toContract = some c2818 := rfl

theorem checked2818 : check 4000 c2818 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2819 : RawOriginal := C022.records[3]'(by decide)
theorem original_id2819 : original2819.index = 2819 := by decide

def c2819 : Contract := original2819.toContract.get (by decide)
theorem binding2819 : original2819.toContract = some c2819 := rfl

theorem checked2819 : check 4000 c2819 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2820 : RawOriginal := C022.records[4]'(by decide)
theorem original_id2820 : original2820.index = 2820 := by decide

def c2820 : Contract := original2820.toContract.get (by decide)
theorem binding2820 : original2820.toContract = some c2820 := rfl

theorem checked2820 : check 4000 c2820 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2821 : RawOriginal := C022.records[5]'(by decide)
theorem original_id2821 : original2821.index = 2821 := by decide

def c2821 : Contract := original2821.toContract.get (by decide)
theorem binding2821 : original2821.toContract = some c2821 := rfl

theorem checked2821 : check 4000 c2821 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2806, c2806, 4000, checked2806⟩,
  ⟨2807, c2807, 4000, checked2807⟩,
  ⟨2808, c2808, 4000, checked2808⟩,
  ⟨2809, c2809, 4000, checked2809⟩,
  ⟨2810, c2810, 4000, checked2810⟩,
  ⟨2811, c2811, 4000, checked2811⟩,
  ⟨2812, c2812, 4000, checked2812⟩,
  ⟨2813, c2813, 4000, checked2813⟩,
  ⟨2814, c2814, 4000, checked2814⟩,
  ⟨2815, c2815, 4000, checked2815⟩,
  ⟨2816, c2816, 4000, checked2816⟩,
  ⟨2817, c2817, 4000, checked2817⟩,
  ⟨2818, c2818, 4000, checked2818⟩,
  ⟨2819, c2819, 4000, checked2819⟩,
  ⟨2820, c2820, 4000, checked2820⟩,
  ⟨2821, c2821, 4000, checked2821⟩]

end PA215.ContractShards.Shard021Part7
