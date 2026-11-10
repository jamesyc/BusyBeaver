import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C039
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard039Part6
open PA215.Contracts PA215.Census

def original5100 : RawOriginal := C039.records[108]'(by decide)
theorem original_id5100 : original5100.index = 5100 := by decide

def c5100 : Contract := original5100.toContract.get (by decide)
theorem binding5100 : original5100.toContract = some c5100 := rfl

theorem checked5100 : check 4000 c5100 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5101 : RawOriginal := C039.records[109]'(by decide)
theorem original_id5101 : original5101.index = 5101 := by decide

def c5101 : Contract := original5101.toContract.get (by decide)
theorem binding5101 : original5101.toContract = some c5101 := rfl

theorem checked5101 : check 4000 c5101 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5102 : RawOriginal := C039.records[110]'(by decide)
theorem original_id5102 : original5102.index = 5102 := by decide

def c5102 : Contract := original5102.toContract.get (by decide)
theorem binding5102 : original5102.toContract = some c5102 := rfl

theorem checked5102 : check 4000 c5102 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5103 : RawOriginal := C039.records[111]'(by decide)
theorem original_id5103 : original5103.index = 5103 := by decide

def c5103 : Contract := original5103.toContract.get (by decide)
theorem binding5103 : original5103.toContract = some c5103 := rfl

theorem checked5103 : check 4000 c5103 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5104 : RawOriginal := C039.records[112]'(by decide)
theorem original_id5104 : original5104.index = 5104 := by decide

def c5104 : Contract := original5104.toContract.get (by decide)
theorem binding5104 : original5104.toContract = some c5104 := rfl

theorem checked5104 : check 4000 c5104 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5105 : RawOriginal := C039.records[113]'(by decide)
theorem original_id5105 : original5105.index = 5105 := by decide

def c5105 : Contract := original5105.toContract.get (by decide)
theorem binding5105 : original5105.toContract = some c5105 := rfl

theorem checked5105 : check 4000 c5105 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5106 : RawOriginal := C039.records[114]'(by decide)
theorem original_id5106 : original5106.index = 5106 := by decide

def c5106 : Contract := original5106.toContract.get (by decide)
theorem binding5106 : original5106.toContract = some c5106 := rfl

theorem checked5106 : check 4000 c5106 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5107 : RawOriginal := C039.records[115]'(by decide)
theorem original_id5107 : original5107.index = 5107 := by decide

def c5107 : Contract := original5107.toContract.get (by decide)
theorem binding5107 : original5107.toContract = some c5107 := rfl

theorem checked5107 : check 4000 c5107 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5108 : RawOriginal := C039.records[116]'(by decide)
theorem original_id5108 : original5108.index = 5108 := by decide

def c5108 : Contract := original5108.toContract.get (by decide)
theorem binding5108 : original5108.toContract = some c5108 := rfl

theorem checked5108 : check 4000 c5108 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5109 : RawOriginal := C039.records[117]'(by decide)
theorem original_id5109 : original5109.index = 5109 := by decide

def c5109 : Contract := original5109.toContract.get (by decide)
theorem binding5109 : original5109.toContract = some c5109 := rfl

theorem checked5109 : check 4000 c5109 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5110 : RawOriginal := C039.records[118]'(by decide)
theorem original_id5110 : original5110.index = 5110 := by decide

def c5110 : Contract := original5110.toContract.get (by decide)
theorem binding5110 : original5110.toContract = some c5110 := rfl

theorem checked5110 : check 4000 c5110 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5111 : RawOriginal := C039.records[119]'(by decide)
theorem original_id5111 : original5111.index = 5111 := by decide

def c5111 : Contract := original5111.toContract.get (by decide)
theorem binding5111 : original5111.toContract = some c5111 := rfl

theorem checked5111 : check 4000 c5111 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5112 : RawOriginal := C039.records[120]'(by decide)
theorem original_id5112 : original5112.index = 5112 := by decide

def c5112 : Contract := original5112.toContract.get (by decide)
theorem binding5112 : original5112.toContract = some c5112 := rfl

theorem checked5112 : check 4000 c5112 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5113 : RawOriginal := C039.records[121]'(by decide)
theorem original_id5113 : original5113.index = 5113 := by decide

def c5113 : Contract := original5113.toContract.get (by decide)
theorem binding5113 : original5113.toContract = some c5113 := rfl

theorem checked5113 : check 4000 c5113 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5115 : RawOriginal := C039.records[123]'(by decide)
theorem original_id5115 : original5115.index = 5115 := by decide

def c5115 : Contract := original5115.toContract.get (by decide)
theorem binding5115 : original5115.toContract = some c5115 := rfl

theorem checked5115 : check 4000 c5115 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5116 : RawOriginal := C039.records[124]'(by decide)
theorem original_id5116 : original5116.index = 5116 := by decide

def c5116 : Contract := original5116.toContract.get (by decide)
theorem binding5116 : original5116.toContract = some c5116 := rfl

theorem checked5116 : check 4000 c5116 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨5100, c5100, 4000, checked5100⟩,
  ⟨5101, c5101, 4000, checked5101⟩,
  ⟨5102, c5102, 4000, checked5102⟩,
  ⟨5103, c5103, 4000, checked5103⟩,
  ⟨5104, c5104, 4000, checked5104⟩,
  ⟨5105, c5105, 4000, checked5105⟩,
  ⟨5106, c5106, 4000, checked5106⟩,
  ⟨5107, c5107, 4000, checked5107⟩,
  ⟨5108, c5108, 4000, checked5108⟩,
  ⟨5109, c5109, 4000, checked5109⟩,
  ⟨5110, c5110, 4000, checked5110⟩,
  ⟨5111, c5111, 4000, checked5111⟩,
  ⟨5112, c5112, 4000, checked5112⟩,
  ⟨5113, c5113, 4000, checked5113⟩,
  ⟨5115, c5115, 4000, checked5115⟩,
  ⟨5116, c5116, 4000, checked5116⟩]

end PA215.ContractShards.Shard039Part6
