import PA215.CertifiedContracts
import PA215.Census.C006
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard006Part2
open PA215.Contracts PA215.Census

def original806 : RawOriginal := C006.records[38]'(by decide)
theorem original_id806 : original806.index = 806 := by decide

def c806 : Contract := original806.toContract.get (by decide)
theorem binding806 : original806.toContract = some c806 := rfl

theorem checked806 : check 4000 c806 = true := by decide

def original807 : RawOriginal := C006.records[39]'(by decide)
theorem original_id807 : original807.index = 807 := by decide

def c807 : Contract := original807.toContract.get (by decide)
theorem binding807 : original807.toContract = some c807 := rfl

theorem checked807 : check 4000 c807 = true := by decide

def original808 : RawOriginal := C006.records[40]'(by decide)
theorem original_id808 : original808.index = 808 := by decide

def c808 : Contract := original808.toContract.get (by decide)
theorem binding808 : original808.toContract = some c808 := rfl

theorem checked808 : check 4000 c808 = true := by decide

def original809 : RawOriginal := C006.records[41]'(by decide)
theorem original_id809 : original809.index = 809 := by decide

def c809 : Contract := original809.toContract.get (by decide)
theorem binding809 : original809.toContract = some c809 := rfl

theorem checked809 : check 4000 c809 = true := by decide

def original810 : RawOriginal := C006.records[42]'(by decide)
theorem original_id810 : original810.index = 810 := by decide

def c810 : Contract := original810.toContract.get (by decide)
theorem binding810 : original810.toContract = some c810 := rfl

theorem checked810 : check 4000 c810 = true := by decide

def original811 : RawOriginal := C006.records[43]'(by decide)
theorem original_id811 : original811.index = 811 := by decide

def c811 : Contract := original811.toContract.get (by decide)
theorem binding811 : original811.toContract = some c811 := rfl

theorem checked811 : check 4000 c811 = true := by decide

def original812 : RawOriginal := C006.records[44]'(by decide)
theorem original_id812 : original812.index = 812 := by decide

def c812 : Contract := original812.toContract.get (by decide)
theorem binding812 : original812.toContract = some c812 := rfl

theorem checked812 : check 4000 c812 = true := by decide

def original813 : RawOriginal := C006.records[45]'(by decide)
theorem original_id813 : original813.index = 813 := by decide

def c813 : Contract := original813.toContract.get (by decide)
theorem binding813 : original813.toContract = some c813 := rfl

theorem checked813 : check 4000 c813 = true := by decide

def original814 : RawOriginal := C006.records[46]'(by decide)
theorem original_id814 : original814.index = 814 := by decide

def c814 : Contract := original814.toContract.get (by decide)
theorem binding814 : original814.toContract = some c814 := rfl

theorem checked814 : check 4000 c814 = true := by decide

def original815 : RawOriginal := C006.records[47]'(by decide)
theorem original_id815 : original815.index = 815 := by decide

def c815 : Contract := original815.toContract.get (by decide)
theorem binding815 : original815.toContract = some c815 := rfl

theorem checked815 : check 4000 c815 = true := by decide

def original816 : RawOriginal := C006.records[48]'(by decide)
theorem original_id816 : original816.index = 816 := by decide

def c816 : Contract := original816.toContract.get (by decide)
theorem binding816 : original816.toContract = some c816 := rfl

theorem checked816 : check 4000 c816 = true := by decide

def original817 : RawOriginal := C006.records[49]'(by decide)
theorem original_id817 : original817.index = 817 := by decide

def c817 : Contract := original817.toContract.get (by decide)
theorem binding817 : original817.toContract = some c817 := rfl

theorem checked817 : check 4000 c817 = true := by decide

def original818 : RawOriginal := C006.records[50]'(by decide)
theorem original_id818 : original818.index = 818 := by decide

def c818 : Contract := original818.toContract.get (by decide)
theorem binding818 : original818.toContract = some c818 := rfl

theorem checked818 : check 4000 c818 = true := by decide

def original819 : RawOriginal := C006.records[51]'(by decide)
theorem original_id819 : original819.index = 819 := by decide

def c819 : Contract := original819.toContract.get (by decide)
theorem binding819 : original819.toContract = some c819 := rfl

theorem checked819 : check 4000 c819 = true := by decide

def original820 : RawOriginal := C006.records[52]'(by decide)
theorem original_id820 : original820.index = 820 := by decide

def c820 : Contract := original820.toContract.get (by decide)
theorem binding820 : original820.toContract = some c820 := rfl

theorem checked820 : check 4000 c820 = true := by decide

def original821 : RawOriginal := C006.records[53]'(by decide)
theorem original_id821 : original821.index = 821 := by decide

def c821 : Contract := original821.toContract.get (by decide)
theorem binding821 : original821.toContract = some c821 := rfl

theorem checked821 : check 4000 c821 = true := by decide

def records : List Certified := [
  ⟨806, c806, 4000, checked806⟩,
  ⟨807, c807, 4000, checked807⟩,
  ⟨808, c808, 4000, checked808⟩,
  ⟨809, c809, 4000, checked809⟩,
  ⟨810, c810, 4000, checked810⟩,
  ⟨811, c811, 4000, checked811⟩,
  ⟨812, c812, 4000, checked812⟩,
  ⟨813, c813, 4000, checked813⟩,
  ⟨814, c814, 4000, checked814⟩,
  ⟨815, c815, 4000, checked815⟩,
  ⟨816, c816, 4000, checked816⟩,
  ⟨817, c817, 4000, checked817⟩,
  ⟨818, c818, 4000, checked818⟩,
  ⟨819, c819, 4000, checked819⟩,
  ⟨820, c820, 4000, checked820⟩,
  ⟨821, c821, 4000, checked821⟩]

end PA215.ContractShards.Shard006Part2
