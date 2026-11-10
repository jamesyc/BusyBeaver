import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C018
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard018Part0
open PA215.Contracts PA215.Census

def original2310 : RawOriginal := C018.records[6]'(by decide)
theorem original_id2310 : original2310.index = 2310 := by decide

def c2310 : Contract := original2310.toContract.get (by decide)
theorem binding2310 : original2310.toContract = some c2310 := rfl

theorem checked2310 : check 4000 c2310 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2311 : RawOriginal := C018.records[7]'(by decide)
theorem original_id2311 : original2311.index = 2311 := by decide

def c2311 : Contract := original2311.toContract.get (by decide)
theorem binding2311 : original2311.toContract = some c2311 := rfl

theorem checked2311 : check 4000 c2311 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2312 : RawOriginal := C018.records[8]'(by decide)
theorem original_id2312 : original2312.index = 2312 := by decide

def c2312 : Contract := original2312.toContract.get (by decide)
theorem binding2312 : original2312.toContract = some c2312 := rfl

theorem checked2312 : check 4000 c2312 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2313 : RawOriginal := C018.records[9]'(by decide)
theorem original_id2313 : original2313.index = 2313 := by decide

def c2313 : Contract := original2313.toContract.get (by decide)
theorem binding2313 : original2313.toContract = some c2313 := rfl

theorem checked2313 : check 4000 c2313 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2314 : RawOriginal := C018.records[10]'(by decide)
theorem original_id2314 : original2314.index = 2314 := by decide

def c2314 : Contract := original2314.toContract.get (by decide)
theorem binding2314 : original2314.toContract = some c2314 := rfl

theorem checked2314 : check 4000 c2314 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2315 : RawOriginal := C018.records[11]'(by decide)
theorem original_id2315 : original2315.index = 2315 := by decide

def c2315 : Contract := original2315.toContract.get (by decide)
theorem binding2315 : original2315.toContract = some c2315 := rfl

theorem checked2315 : check 4000 c2315 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2316 : RawOriginal := C018.records[12]'(by decide)
theorem original_id2316 : original2316.index = 2316 := by decide

def c2316 : Contract := original2316.toContract.get (by decide)
theorem binding2316 : original2316.toContract = some c2316 := rfl

theorem checked2316 : check 4000 c2316 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2317 : RawOriginal := C018.records[13]'(by decide)
theorem original_id2317 : original2317.index = 2317 := by decide

def c2317 : Contract := original2317.toContract.get (by decide)
theorem binding2317 : original2317.toContract = some c2317 := rfl

theorem checked2317 : check 4000 c2317 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2318 : RawOriginal := C018.records[14]'(by decide)
theorem original_id2318 : original2318.index = 2318 := by decide

def c2318 : Contract := original2318.toContract.get (by decide)
theorem binding2318 : original2318.toContract = some c2318 := rfl

theorem checked2318 : check 4000 c2318 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2319 : RawOriginal := C018.records[15]'(by decide)
theorem original_id2319 : original2319.index = 2319 := by decide

def c2319 : Contract := original2319.toContract.get (by decide)
theorem binding2319 : original2319.toContract = some c2319 := rfl

theorem checked2319 : check 4000 c2319 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2320 : RawOriginal := C018.records[16]'(by decide)
theorem original_id2320 : original2320.index = 2320 := by decide

def c2320 : Contract := original2320.toContract.get (by decide)
theorem binding2320 : original2320.toContract = some c2320 := rfl

theorem checked2320 : check 4000 c2320 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2321 : RawOriginal := C018.records[17]'(by decide)
theorem original_id2321 : original2321.index = 2321 := by decide

def c2321 : Contract := original2321.toContract.get (by decide)
theorem binding2321 : original2321.toContract = some c2321 := rfl

theorem checked2321 : check 4000 c2321 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2322 : RawOriginal := C018.records[18]'(by decide)
theorem original_id2322 : original2322.index = 2322 := by decide

def c2322 : Contract := original2322.toContract.get (by decide)
theorem binding2322 : original2322.toContract = some c2322 := rfl

theorem checked2322 : check 4000 c2322 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2323 : RawOriginal := C018.records[19]'(by decide)
theorem original_id2323 : original2323.index = 2323 := by decide

def c2323 : Contract := original2323.toContract.get (by decide)
theorem binding2323 : original2323.toContract = some c2323 := rfl

theorem checked2323 : check 4000 c2323 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2324 : RawOriginal := C018.records[20]'(by decide)
theorem original_id2324 : original2324.index = 2324 := by decide

def c2324 : Contract := original2324.toContract.get (by decide)
theorem binding2324 : original2324.toContract = some c2324 := rfl

theorem checked2324 : check 4000 c2324 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2325 : RawOriginal := C018.records[21]'(by decide)
theorem original_id2325 : original2325.index = 2325 := by decide

def c2325 : Contract := original2325.toContract.get (by decide)
theorem binding2325 : original2325.toContract = some c2325 := rfl

theorem checked2325 : check 4000 c2325 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2310, c2310, 4000, checked2310⟩,
  ⟨2311, c2311, 4000, checked2311⟩,
  ⟨2312, c2312, 4000, checked2312⟩,
  ⟨2313, c2313, 4000, checked2313⟩,
  ⟨2314, c2314, 4000, checked2314⟩,
  ⟨2315, c2315, 4000, checked2315⟩,
  ⟨2316, c2316, 4000, checked2316⟩,
  ⟨2317, c2317, 4000, checked2317⟩,
  ⟨2318, c2318, 4000, checked2318⟩,
  ⟨2319, c2319, 4000, checked2319⟩,
  ⟨2320, c2320, 4000, checked2320⟩,
  ⟨2321, c2321, 4000, checked2321⟩,
  ⟨2322, c2322, 4000, checked2322⟩,
  ⟨2323, c2323, 4000, checked2323⟩,
  ⟨2324, c2324, 4000, checked2324⟩,
  ⟨2325, c2325, 4000, checked2325⟩]

end PA215.ContractShards.Shard018Part0
