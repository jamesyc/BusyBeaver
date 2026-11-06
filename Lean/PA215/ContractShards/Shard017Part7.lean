import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C017
import PA215.Census.C018
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard017Part7
open PA215.Contracts PA215.Census

def original2294 : RawOriginal := C017.records[118]'(by decide)
theorem original_id2294 : original2294.index = 2294 := by decide

def c2294 : Contract := original2294.toContract.get (by decide)
theorem binding2294 : original2294.toContract = some c2294 := rfl

theorem checked2294 : check 4000 c2294 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2295 : RawOriginal := C017.records[119]'(by decide)
theorem original_id2295 : original2295.index = 2295 := by decide

def c2295 : Contract := original2295.toContract.get (by decide)
theorem binding2295 : original2295.toContract = some c2295 := rfl

theorem checked2295 : check 4000 c2295 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2296 : RawOriginal := C017.records[120]'(by decide)
theorem original_id2296 : original2296.index = 2296 := by decide

def c2296 : Contract := original2296.toContract.get (by decide)
theorem binding2296 : original2296.toContract = some c2296 := rfl

theorem checked2296 : check 4000 c2296 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2297 : RawOriginal := C017.records[121]'(by decide)
theorem original_id2297 : original2297.index = 2297 := by decide

def c2297 : Contract := original2297.toContract.get (by decide)
theorem binding2297 : original2297.toContract = some c2297 := rfl

theorem checked2297 : check 4000 c2297 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2298 : RawOriginal := C017.records[122]'(by decide)
theorem original_id2298 : original2298.index = 2298 := by decide

def c2298 : Contract := original2298.toContract.get (by decide)
theorem binding2298 : original2298.toContract = some c2298 := rfl

theorem checked2298 : check 4000 c2298 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2299 : RawOriginal := C017.records[123]'(by decide)
theorem original_id2299 : original2299.index = 2299 := by decide

def c2299 : Contract := original2299.toContract.get (by decide)
theorem binding2299 : original2299.toContract = some c2299 := rfl

theorem checked2299 : check 4000 c2299 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2300 : RawOriginal := C017.records[124]'(by decide)
theorem original_id2300 : original2300.index = 2300 := by decide

def c2300 : Contract := original2300.toContract.get (by decide)
theorem binding2300 : original2300.toContract = some c2300 := rfl

theorem checked2300 : check 4000 c2300 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2301 : RawOriginal := C017.records[125]'(by decide)
theorem original_id2301 : original2301.index = 2301 := by decide

def c2301 : Contract := original2301.toContract.get (by decide)
theorem binding2301 : original2301.toContract = some c2301 := rfl

theorem checked2301 : check 4000 c2301 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2302 : RawOriginal := C017.records[126]'(by decide)
theorem original_id2302 : original2302.index = 2302 := by decide

def c2302 : Contract := original2302.toContract.get (by decide)
theorem binding2302 : original2302.toContract = some c2302 := rfl

theorem checked2302 : check 4000 c2302 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2303 : RawOriginal := C017.records[127]'(by decide)
theorem original_id2303 : original2303.index = 2303 := by decide

def c2303 : Contract := original2303.toContract.get (by decide)
theorem binding2303 : original2303.toContract = some c2303 := rfl

theorem checked2303 : check 4000 c2303 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2304 : RawOriginal := C018.records[0]'(by decide)
theorem original_id2304 : original2304.index = 2304 := by decide

def c2304 : Contract := original2304.toContract.get (by decide)
theorem binding2304 : original2304.toContract = some c2304 := rfl

theorem checked2304 : check 4000 c2304 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2305 : RawOriginal := C018.records[1]'(by decide)
theorem original_id2305 : original2305.index = 2305 := by decide

def c2305 : Contract := original2305.toContract.get (by decide)
theorem binding2305 : original2305.toContract = some c2305 := rfl

theorem checked2305 : check 4000 c2305 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2306 : RawOriginal := C018.records[2]'(by decide)
theorem original_id2306 : original2306.index = 2306 := by decide

def c2306 : Contract := original2306.toContract.get (by decide)
theorem binding2306 : original2306.toContract = some c2306 := rfl

theorem checked2306 : check 4000 c2306 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2307 : RawOriginal := C018.records[3]'(by decide)
theorem original_id2307 : original2307.index = 2307 := by decide

def c2307 : Contract := original2307.toContract.get (by decide)
theorem binding2307 : original2307.toContract = some c2307 := rfl

theorem checked2307 : check 4000 c2307 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2308 : RawOriginal := C018.records[4]'(by decide)
theorem original_id2308 : original2308.index = 2308 := by decide

def c2308 : Contract := original2308.toContract.get (by decide)
theorem binding2308 : original2308.toContract = some c2308 := rfl

theorem checked2308 : check 4000 c2308 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2309 : RawOriginal := C018.records[5]'(by decide)
theorem original_id2309 : original2309.index = 2309 := by decide

def c2309 : Contract := original2309.toContract.get (by decide)
theorem binding2309 : original2309.toContract = some c2309 := rfl

theorem checked2309 : check 4000 c2309 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2294, c2294, 4000, checked2294⟩,
  ⟨2295, c2295, 4000, checked2295⟩,
  ⟨2296, c2296, 4000, checked2296⟩,
  ⟨2297, c2297, 4000, checked2297⟩,
  ⟨2298, c2298, 4000, checked2298⟩,
  ⟨2299, c2299, 4000, checked2299⟩,
  ⟨2300, c2300, 4000, checked2300⟩,
  ⟨2301, c2301, 4000, checked2301⟩,
  ⟨2302, c2302, 4000, checked2302⟩,
  ⟨2303, c2303, 4000, checked2303⟩,
  ⟨2304, c2304, 4000, checked2304⟩,
  ⟨2305, c2305, 4000, checked2305⟩,
  ⟨2306, c2306, 4000, checked2306⟩,
  ⟨2307, c2307, 4000, checked2307⟩,
  ⟨2308, c2308, 4000, checked2308⟩,
  ⟨2309, c2309, 4000, checked2309⟩]

end PA215.ContractShards.Shard017Part7
