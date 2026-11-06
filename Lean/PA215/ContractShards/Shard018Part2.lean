import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C018
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard018Part2
open PA215.Contracts PA215.Census

def original2342 : RawOriginal := C018.records[38]'(by decide)
theorem original_id2342 : original2342.index = 2342 := by decide

def c2342 : Contract := original2342.toContract.get (by decide)
theorem binding2342 : original2342.toContract = some c2342 := rfl

theorem checked2342 : check 4000 c2342 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2343 : RawOriginal := C018.records[39]'(by decide)
theorem original_id2343 : original2343.index = 2343 := by decide

def c2343 : Contract := original2343.toContract.get (by decide)
theorem binding2343 : original2343.toContract = some c2343 := rfl

theorem checked2343 : check 4000 c2343 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2344 : RawOriginal := C018.records[40]'(by decide)
theorem original_id2344 : original2344.index = 2344 := by decide

def c2344 : Contract := original2344.toContract.get (by decide)
theorem binding2344 : original2344.toContract = some c2344 := rfl

theorem checked2344 : check 4000 c2344 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2345 : RawOriginal := C018.records[41]'(by decide)
theorem original_id2345 : original2345.index = 2345 := by decide

def c2345 : Contract := original2345.toContract.get (by decide)
theorem binding2345 : original2345.toContract = some c2345 := rfl

theorem checked2345 : check 4000 c2345 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2346 : RawOriginal := C018.records[42]'(by decide)
theorem original_id2346 : original2346.index = 2346 := by decide

def c2346 : Contract := original2346.toContract.get (by decide)
theorem binding2346 : original2346.toContract = some c2346 := rfl

theorem checked2346 : check 4000 c2346 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2347 : RawOriginal := C018.records[43]'(by decide)
theorem original_id2347 : original2347.index = 2347 := by decide

def c2347 : Contract := original2347.toContract.get (by decide)
theorem binding2347 : original2347.toContract = some c2347 := rfl

theorem checked2347 : check 4000 c2347 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2348 : RawOriginal := C018.records[44]'(by decide)
theorem original_id2348 : original2348.index = 2348 := by decide

def c2348 : Contract := original2348.toContract.get (by decide)
theorem binding2348 : original2348.toContract = some c2348 := rfl

theorem checked2348 : check 4000 c2348 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2349 : RawOriginal := C018.records[45]'(by decide)
theorem original_id2349 : original2349.index = 2349 := by decide

def c2349 : Contract := original2349.toContract.get (by decide)
theorem binding2349 : original2349.toContract = some c2349 := rfl

theorem checked2349 : check 4000 c2349 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2350 : RawOriginal := C018.records[46]'(by decide)
theorem original_id2350 : original2350.index = 2350 := by decide

def c2350 : Contract := original2350.toContract.get (by decide)
theorem binding2350 : original2350.toContract = some c2350 := rfl

theorem checked2350 : check 4000 c2350 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2351 : RawOriginal := C018.records[47]'(by decide)
theorem original_id2351 : original2351.index = 2351 := by decide

def c2351 : Contract := original2351.toContract.get (by decide)
theorem binding2351 : original2351.toContract = some c2351 := rfl

theorem checked2351 : check 4000 c2351 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2352 : RawOriginal := C018.records[48]'(by decide)
theorem original_id2352 : original2352.index = 2352 := by decide

def c2352 : Contract := original2352.toContract.get (by decide)
theorem binding2352 : original2352.toContract = some c2352 := rfl

theorem checked2352 : check 4000 c2352 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2353 : RawOriginal := C018.records[49]'(by decide)
theorem original_id2353 : original2353.index = 2353 := by decide

def c2353 : Contract := original2353.toContract.get (by decide)
theorem binding2353 : original2353.toContract = some c2353 := rfl

theorem checked2353 : check 4000 c2353 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2354 : RawOriginal := C018.records[50]'(by decide)
theorem original_id2354 : original2354.index = 2354 := by decide

def c2354 : Contract := original2354.toContract.get (by decide)
theorem binding2354 : original2354.toContract = some c2354 := rfl

theorem checked2354 : check 4000 c2354 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2355 : RawOriginal := C018.records[51]'(by decide)
theorem original_id2355 : original2355.index = 2355 := by decide

def c2355 : Contract := original2355.toContract.get (by decide)
theorem binding2355 : original2355.toContract = some c2355 := rfl

theorem checked2355 : check 4000 c2355 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2356 : RawOriginal := C018.records[52]'(by decide)
theorem original_id2356 : original2356.index = 2356 := by decide

def c2356 : Contract := original2356.toContract.get (by decide)
theorem binding2356 : original2356.toContract = some c2356 := rfl

theorem checked2356 : check 4000 c2356 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2357 : RawOriginal := C018.records[53]'(by decide)
theorem original_id2357 : original2357.index = 2357 := by decide

def c2357 : Contract := original2357.toContract.get (by decide)
theorem binding2357 : original2357.toContract = some c2357 := rfl

theorem checked2357 : check 4000 c2357 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2342, c2342, 4000, checked2342⟩,
  ⟨2343, c2343, 4000, checked2343⟩,
  ⟨2344, c2344, 4000, checked2344⟩,
  ⟨2345, c2345, 4000, checked2345⟩,
  ⟨2346, c2346, 4000, checked2346⟩,
  ⟨2347, c2347, 4000, checked2347⟩,
  ⟨2348, c2348, 4000, checked2348⟩,
  ⟨2349, c2349, 4000, checked2349⟩,
  ⟨2350, c2350, 4000, checked2350⟩,
  ⟨2351, c2351, 4000, checked2351⟩,
  ⟨2352, c2352, 4000, checked2352⟩,
  ⟨2353, c2353, 4000, checked2353⟩,
  ⟨2354, c2354, 4000, checked2354⟩,
  ⟨2355, c2355, 4000, checked2355⟩,
  ⟨2356, c2356, 4000, checked2356⟩,
  ⟨2357, c2357, 4000, checked2357⟩]

end PA215.ContractShards.Shard018Part2
