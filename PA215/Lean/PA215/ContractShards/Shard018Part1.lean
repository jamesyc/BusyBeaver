import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C018
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard018Part1
open PA215.Contracts PA215.Census

def original2326 : RawOriginal := C018.records[22]'(by decide)
theorem original_id2326 : original2326.index = 2326 := by decide

def c2326 : Contract := original2326.toContract.get (by decide)
theorem binding2326 : original2326.toContract = some c2326 := rfl

theorem checked2326 : check 4000 c2326 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2327 : RawOriginal := C018.records[23]'(by decide)
theorem original_id2327 : original2327.index = 2327 := by decide

def c2327 : Contract := original2327.toContract.get (by decide)
theorem binding2327 : original2327.toContract = some c2327 := rfl

theorem checked2327 : check 4000 c2327 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2328 : RawOriginal := C018.records[24]'(by decide)
theorem original_id2328 : original2328.index = 2328 := by decide

def c2328 : Contract := original2328.toContract.get (by decide)
theorem binding2328 : original2328.toContract = some c2328 := rfl

theorem checked2328 : check 4000 c2328 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2329 : RawOriginal := C018.records[25]'(by decide)
theorem original_id2329 : original2329.index = 2329 := by decide

def c2329 : Contract := original2329.toContract.get (by decide)
theorem binding2329 : original2329.toContract = some c2329 := rfl

theorem checked2329 : check 4000 c2329 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2330 : RawOriginal := C018.records[26]'(by decide)
theorem original_id2330 : original2330.index = 2330 := by decide

def c2330 : Contract := original2330.toContract.get (by decide)
theorem binding2330 : original2330.toContract = some c2330 := rfl

theorem checked2330 : check 4000 c2330 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2331 : RawOriginal := C018.records[27]'(by decide)
theorem original_id2331 : original2331.index = 2331 := by decide

def c2331 : Contract := original2331.toContract.get (by decide)
theorem binding2331 : original2331.toContract = some c2331 := rfl

theorem checked2331 : check 4000 c2331 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2332 : RawOriginal := C018.records[28]'(by decide)
theorem original_id2332 : original2332.index = 2332 := by decide

def c2332 : Contract := original2332.toContract.get (by decide)
theorem binding2332 : original2332.toContract = some c2332 := rfl

theorem checked2332 : check 4000 c2332 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2333 : RawOriginal := C018.records[29]'(by decide)
theorem original_id2333 : original2333.index = 2333 := by decide

def c2333 : Contract := original2333.toContract.get (by decide)
theorem binding2333 : original2333.toContract = some c2333 := rfl

theorem checked2333 : check 4000 c2333 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2334 : RawOriginal := C018.records[30]'(by decide)
theorem original_id2334 : original2334.index = 2334 := by decide

def c2334 : Contract := original2334.toContract.get (by decide)
theorem binding2334 : original2334.toContract = some c2334 := rfl

theorem checked2334 : check 4000 c2334 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2335 : RawOriginal := C018.records[31]'(by decide)
theorem original_id2335 : original2335.index = 2335 := by decide

def c2335 : Contract := original2335.toContract.get (by decide)
theorem binding2335 : original2335.toContract = some c2335 := rfl

theorem checked2335 : check 4000 c2335 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2336 : RawOriginal := C018.records[32]'(by decide)
theorem original_id2336 : original2336.index = 2336 := by decide

def c2336 : Contract := original2336.toContract.get (by decide)
theorem binding2336 : original2336.toContract = some c2336 := rfl

theorem checked2336 : check 4000 c2336 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2337 : RawOriginal := C018.records[33]'(by decide)
theorem original_id2337 : original2337.index = 2337 := by decide

def c2337 : Contract := original2337.toContract.get (by decide)
theorem binding2337 : original2337.toContract = some c2337 := rfl

theorem checked2337 : check 4000 c2337 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2338 : RawOriginal := C018.records[34]'(by decide)
theorem original_id2338 : original2338.index = 2338 := by decide

def c2338 : Contract := original2338.toContract.get (by decide)
theorem binding2338 : original2338.toContract = some c2338 := rfl

theorem checked2338 : check 4000 c2338 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2339 : RawOriginal := C018.records[35]'(by decide)
theorem original_id2339 : original2339.index = 2339 := by decide

def c2339 : Contract := original2339.toContract.get (by decide)
theorem binding2339 : original2339.toContract = some c2339 := rfl

theorem checked2339 : check 4000 c2339 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2340 : RawOriginal := C018.records[36]'(by decide)
theorem original_id2340 : original2340.index = 2340 := by decide

def c2340 : Contract := original2340.toContract.get (by decide)
theorem binding2340 : original2340.toContract = some c2340 := rfl

theorem checked2340 : check 4000 c2340 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2341 : RawOriginal := C018.records[37]'(by decide)
theorem original_id2341 : original2341.index = 2341 := by decide

def c2341 : Contract := original2341.toContract.get (by decide)
theorem binding2341 : original2341.toContract = some c2341 := rfl

theorem checked2341 : check 4000 c2341 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2326, c2326, 4000, checked2326⟩,
  ⟨2327, c2327, 4000, checked2327⟩,
  ⟨2328, c2328, 4000, checked2328⟩,
  ⟨2329, c2329, 4000, checked2329⟩,
  ⟨2330, c2330, 4000, checked2330⟩,
  ⟨2331, c2331, 4000, checked2331⟩,
  ⟨2332, c2332, 4000, checked2332⟩,
  ⟨2333, c2333, 4000, checked2333⟩,
  ⟨2334, c2334, 4000, checked2334⟩,
  ⟨2335, c2335, 4000, checked2335⟩,
  ⟨2336, c2336, 4000, checked2336⟩,
  ⟨2337, c2337, 4000, checked2337⟩,
  ⟨2338, c2338, 4000, checked2338⟩,
  ⟨2339, c2339, 4000, checked2339⟩,
  ⟨2340, c2340, 4000, checked2340⟩,
  ⟨2341, c2341, 4000, checked2341⟩]

end PA215.ContractShards.Shard018Part1
