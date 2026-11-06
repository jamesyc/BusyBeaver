import PA215.CertifiedContracts
import PA215.Census.C006
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard006Part3
open PA215.Contracts PA215.Census

def original822 : RawOriginal := C006.records[54]'(by decide)
theorem original_id822 : original822.index = 822 := by decide

def c822 : Contract := original822.toContract.get (by decide)
theorem binding822 : original822.toContract = some c822 := rfl

theorem checked822 : check 4000 c822 = true := by decide

def original823 : RawOriginal := C006.records[55]'(by decide)
theorem original_id823 : original823.index = 823 := by decide

def c823 : Contract := original823.toContract.get (by decide)
theorem binding823 : original823.toContract = some c823 := rfl

theorem checked823 : check 4000 c823 = true := by decide

def original824 : RawOriginal := C006.records[56]'(by decide)
theorem original_id824 : original824.index = 824 := by decide

def c824 : Contract := original824.toContract.get (by decide)
theorem binding824 : original824.toContract = some c824 := rfl

theorem checked824 : check 4000 c824 = true := by decide

def original825 : RawOriginal := C006.records[57]'(by decide)
theorem original_id825 : original825.index = 825 := by decide

def c825 : Contract := original825.toContract.get (by decide)
theorem binding825 : original825.toContract = some c825 := rfl

theorem checked825 : check 4000 c825 = true := by decide

def original826 : RawOriginal := C006.records[58]'(by decide)
theorem original_id826 : original826.index = 826 := by decide

def c826 : Contract := original826.toContract.get (by decide)
theorem binding826 : original826.toContract = some c826 := rfl

theorem checked826 : check 4000 c826 = true := by decide

def original827 : RawOriginal := C006.records[59]'(by decide)
theorem original_id827 : original827.index = 827 := by decide

def c827 : Contract := original827.toContract.get (by decide)
theorem binding827 : original827.toContract = some c827 := rfl

theorem checked827 : check 4000 c827 = true := by decide

def original828 : RawOriginal := C006.records[60]'(by decide)
theorem original_id828 : original828.index = 828 := by decide

def c828 : Contract := original828.toContract.get (by decide)
theorem binding828 : original828.toContract = some c828 := rfl

theorem checked828 : check 4000 c828 = true := by decide

def original829 : RawOriginal := C006.records[61]'(by decide)
theorem original_id829 : original829.index = 829 := by decide

def c829 : Contract := original829.toContract.get (by decide)
theorem binding829 : original829.toContract = some c829 := rfl

theorem checked829 : check 4000 c829 = true := by decide

def original830 : RawOriginal := C006.records[62]'(by decide)
theorem original_id830 : original830.index = 830 := by decide

def c830 : Contract := original830.toContract.get (by decide)
theorem binding830 : original830.toContract = some c830 := rfl

theorem checked830 : check 4000 c830 = true := by decide

def original831 : RawOriginal := C006.records[63]'(by decide)
theorem original_id831 : original831.index = 831 := by decide

def c831 : Contract := original831.toContract.get (by decide)
theorem binding831 : original831.toContract = some c831 := rfl

theorem checked831 : check 4000 c831 = true := by decide

def original832 : RawOriginal := C006.records[64]'(by decide)
theorem original_id832 : original832.index = 832 := by decide

def c832 : Contract := original832.toContract.get (by decide)
theorem binding832 : original832.toContract = some c832 := rfl

theorem checked832 : check 4000 c832 = true := by decide

def original833 : RawOriginal := C006.records[65]'(by decide)
theorem original_id833 : original833.index = 833 := by decide

def c833 : Contract := original833.toContract.get (by decide)
theorem binding833 : original833.toContract = some c833 := rfl

theorem checked833 : check 4000 c833 = true := by decide

def original834 : RawOriginal := C006.records[66]'(by decide)
theorem original_id834 : original834.index = 834 := by decide

def c834 : Contract := original834.toContract.get (by decide)
theorem binding834 : original834.toContract = some c834 := rfl

theorem checked834 : check 4000 c834 = true := by decide

def original835 : RawOriginal := C006.records[67]'(by decide)
theorem original_id835 : original835.index = 835 := by decide

def c835 : Contract := original835.toContract.get (by decide)
theorem binding835 : original835.toContract = some c835 := rfl

theorem checked835 : check 4000 c835 = true := by decide

def original836 : RawOriginal := C006.records[68]'(by decide)
theorem original_id836 : original836.index = 836 := by decide

def c836 : Contract := original836.toContract.get (by decide)
theorem binding836 : original836.toContract = some c836 := rfl

theorem checked836 : check 4000 c836 = true := by decide

def original837 : RawOriginal := C006.records[69]'(by decide)
theorem original_id837 : original837.index = 837 := by decide

def c837 : Contract := original837.toContract.get (by decide)
theorem binding837 : original837.toContract = some c837 := rfl

theorem checked837 : check 4000 c837 = true := by decide

def records : List Certified := [
  ⟨822, c822, 4000, checked822⟩,
  ⟨823, c823, 4000, checked823⟩,
  ⟨824, c824, 4000, checked824⟩,
  ⟨825, c825, 4000, checked825⟩,
  ⟨826, c826, 4000, checked826⟩,
  ⟨827, c827, 4000, checked827⟩,
  ⟨828, c828, 4000, checked828⟩,
  ⟨829, c829, 4000, checked829⟩,
  ⟨830, c830, 4000, checked830⟩,
  ⟨831, c831, 4000, checked831⟩,
  ⟨832, c832, 4000, checked832⟩,
  ⟨833, c833, 4000, checked833⟩,
  ⟨834, c834, 4000, checked834⟩,
  ⟨835, c835, 4000, checked835⟩,
  ⟨836, c836, 4000, checked836⟩,
  ⟨837, c837, 4000, checked837⟩]

end PA215.ContractShards.Shard006Part3
