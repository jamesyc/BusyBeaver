import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C017
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard017Part1
open PA215.Contracts PA215.Census

def original2198 : RawOriginal := C017.records[22]'(by decide)
theorem original_id2198 : original2198.index = 2198 := by decide

def c2198 : Contract := original2198.toContract.get (by decide)
theorem binding2198 : original2198.toContract = some c2198 := rfl

theorem checked2198 : check 4000 c2198 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2199 : RawOriginal := C017.records[23]'(by decide)
theorem original_id2199 : original2199.index = 2199 := by decide

def c2199 : Contract := original2199.toContract.get (by decide)
theorem binding2199 : original2199.toContract = some c2199 := rfl

theorem checked2199 : check 4000 c2199 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2200 : RawOriginal := C017.records[24]'(by decide)
theorem original_id2200 : original2200.index = 2200 := by decide

def c2200 : Contract := original2200.toContract.get (by decide)
theorem binding2200 : original2200.toContract = some c2200 := rfl

theorem checked2200 : check 4000 c2200 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2201 : RawOriginal := C017.records[25]'(by decide)
theorem original_id2201 : original2201.index = 2201 := by decide

def c2201 : Contract := original2201.toContract.get (by decide)
theorem binding2201 : original2201.toContract = some c2201 := rfl

theorem checked2201 : check 4000 c2201 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2202 : RawOriginal := C017.records[26]'(by decide)
theorem original_id2202 : original2202.index = 2202 := by decide

def c2202 : Contract := original2202.toContract.get (by decide)
theorem binding2202 : original2202.toContract = some c2202 := rfl

theorem checked2202 : check 4000 c2202 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2203 : RawOriginal := C017.records[27]'(by decide)
theorem original_id2203 : original2203.index = 2203 := by decide

def c2203 : Contract := original2203.toContract.get (by decide)
theorem binding2203 : original2203.toContract = some c2203 := rfl

theorem checked2203 : check 4000 c2203 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2204 : RawOriginal := C017.records[28]'(by decide)
theorem original_id2204 : original2204.index = 2204 := by decide

def c2204 : Contract := original2204.toContract.get (by decide)
theorem binding2204 : original2204.toContract = some c2204 := rfl

theorem checked2204 : check 4000 c2204 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2205 : RawOriginal := C017.records[29]'(by decide)
theorem original_id2205 : original2205.index = 2205 := by decide

def c2205 : Contract := original2205.toContract.get (by decide)
theorem binding2205 : original2205.toContract = some c2205 := rfl

theorem checked2205 : check 4000 c2205 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2206 : RawOriginal := C017.records[30]'(by decide)
theorem original_id2206 : original2206.index = 2206 := by decide

def c2206 : Contract := original2206.toContract.get (by decide)
theorem binding2206 : original2206.toContract = some c2206 := rfl

theorem checked2206 : check 4000 c2206 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2207 : RawOriginal := C017.records[31]'(by decide)
theorem original_id2207 : original2207.index = 2207 := by decide

def c2207 : Contract := original2207.toContract.get (by decide)
theorem binding2207 : original2207.toContract = some c2207 := rfl

theorem checked2207 : check 4000 c2207 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2208 : RawOriginal := C017.records[32]'(by decide)
theorem original_id2208 : original2208.index = 2208 := by decide

def c2208 : Contract := original2208.toContract.get (by decide)
theorem binding2208 : original2208.toContract = some c2208 := rfl

theorem checked2208 : check 4000 c2208 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2209 : RawOriginal := C017.records[33]'(by decide)
theorem original_id2209 : original2209.index = 2209 := by decide

def c2209 : Contract := original2209.toContract.get (by decide)
theorem binding2209 : original2209.toContract = some c2209 := rfl

theorem checked2209 : check 4000 c2209 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2210 : RawOriginal := C017.records[34]'(by decide)
theorem original_id2210 : original2210.index = 2210 := by decide

def c2210 : Contract := original2210.toContract.get (by decide)
theorem binding2210 : original2210.toContract = some c2210 := rfl

theorem checked2210 : check 4000 c2210 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2211 : RawOriginal := C017.records[35]'(by decide)
theorem original_id2211 : original2211.index = 2211 := by decide

def c2211 : Contract := original2211.toContract.get (by decide)
theorem binding2211 : original2211.toContract = some c2211 := rfl

theorem checked2211 : check 4000 c2211 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2212 : RawOriginal := C017.records[36]'(by decide)
theorem original_id2212 : original2212.index = 2212 := by decide

def c2212 : Contract := original2212.toContract.get (by decide)
theorem binding2212 : original2212.toContract = some c2212 := rfl

theorem checked2212 : check 4000 c2212 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2213 : RawOriginal := C017.records[37]'(by decide)
theorem original_id2213 : original2213.index = 2213 := by decide

def c2213 : Contract := original2213.toContract.get (by decide)
theorem binding2213 : original2213.toContract = some c2213 := rfl

theorem checked2213 : check 4000 c2213 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2198, c2198, 4000, checked2198⟩,
  ⟨2199, c2199, 4000, checked2199⟩,
  ⟨2200, c2200, 4000, checked2200⟩,
  ⟨2201, c2201, 4000, checked2201⟩,
  ⟨2202, c2202, 4000, checked2202⟩,
  ⟨2203, c2203, 4000, checked2203⟩,
  ⟨2204, c2204, 4000, checked2204⟩,
  ⟨2205, c2205, 4000, checked2205⟩,
  ⟨2206, c2206, 4000, checked2206⟩,
  ⟨2207, c2207, 4000, checked2207⟩,
  ⟨2208, c2208, 4000, checked2208⟩,
  ⟨2209, c2209, 4000, checked2209⟩,
  ⟨2210, c2210, 4000, checked2210⟩,
  ⟨2211, c2211, 4000, checked2211⟩,
  ⟨2212, c2212, 4000, checked2212⟩,
  ⟨2213, c2213, 4000, checked2213⟩]

end PA215.ContractShards.Shard017Part1
