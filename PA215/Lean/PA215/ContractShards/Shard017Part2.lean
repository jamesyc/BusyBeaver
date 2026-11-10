import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C017
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard017Part2
open PA215.Contracts PA215.Census

def original2214 : RawOriginal := C017.records[38]'(by decide)
theorem original_id2214 : original2214.index = 2214 := by decide

def c2214 : Contract := original2214.toContract.get (by decide)
theorem binding2214 : original2214.toContract = some c2214 := rfl

theorem checked2214 : check 4000 c2214 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2215 : RawOriginal := C017.records[39]'(by decide)
theorem original_id2215 : original2215.index = 2215 := by decide

def c2215 : Contract := original2215.toContract.get (by decide)
theorem binding2215 : original2215.toContract = some c2215 := rfl

theorem checked2215 : check 4000 c2215 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2216 : RawOriginal := C017.records[40]'(by decide)
theorem original_id2216 : original2216.index = 2216 := by decide

def c2216 : Contract := original2216.toContract.get (by decide)
theorem binding2216 : original2216.toContract = some c2216 := rfl

theorem checked2216 : check 4000 c2216 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2217 : RawOriginal := C017.records[41]'(by decide)
theorem original_id2217 : original2217.index = 2217 := by decide

def c2217 : Contract := original2217.toContract.get (by decide)
theorem binding2217 : original2217.toContract = some c2217 := rfl

theorem checked2217 : check 4000 c2217 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2218 : RawOriginal := C017.records[42]'(by decide)
theorem original_id2218 : original2218.index = 2218 := by decide

def c2218 : Contract := original2218.toContract.get (by decide)
theorem binding2218 : original2218.toContract = some c2218 := rfl

theorem checked2218 : check 4000 c2218 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2219 : RawOriginal := C017.records[43]'(by decide)
theorem original_id2219 : original2219.index = 2219 := by decide

def c2219 : Contract := original2219.toContract.get (by decide)
theorem binding2219 : original2219.toContract = some c2219 := rfl

theorem checked2219 : check 4000 c2219 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2220 : RawOriginal := C017.records[44]'(by decide)
theorem original_id2220 : original2220.index = 2220 := by decide

def c2220 : Contract := original2220.toContract.get (by decide)
theorem binding2220 : original2220.toContract = some c2220 := rfl

theorem checked2220 : check 4000 c2220 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2221 : RawOriginal := C017.records[45]'(by decide)
theorem original_id2221 : original2221.index = 2221 := by decide

def c2221 : Contract := original2221.toContract.get (by decide)
theorem binding2221 : original2221.toContract = some c2221 := rfl

theorem checked2221 : check 4000 c2221 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2222 : RawOriginal := C017.records[46]'(by decide)
theorem original_id2222 : original2222.index = 2222 := by decide

def c2222 : Contract := original2222.toContract.get (by decide)
theorem binding2222 : original2222.toContract = some c2222 := rfl

theorem checked2222 : check 4000 c2222 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2223 : RawOriginal := C017.records[47]'(by decide)
theorem original_id2223 : original2223.index = 2223 := by decide

def c2223 : Contract := original2223.toContract.get (by decide)
theorem binding2223 : original2223.toContract = some c2223 := rfl

theorem checked2223 : check 4000 c2223 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2224 : RawOriginal := C017.records[48]'(by decide)
theorem original_id2224 : original2224.index = 2224 := by decide

def c2224 : Contract := original2224.toContract.get (by decide)
theorem binding2224 : original2224.toContract = some c2224 := rfl

theorem checked2224 : check 4000 c2224 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2225 : RawOriginal := C017.records[49]'(by decide)
theorem original_id2225 : original2225.index = 2225 := by decide

def c2225 : Contract := original2225.toContract.get (by decide)
theorem binding2225 : original2225.toContract = some c2225 := rfl

theorem checked2225 : check 4000 c2225 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2226 : RawOriginal := C017.records[50]'(by decide)
theorem original_id2226 : original2226.index = 2226 := by decide

def c2226 : Contract := original2226.toContract.get (by decide)
theorem binding2226 : original2226.toContract = some c2226 := rfl

theorem checked2226 : check 4000 c2226 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2227 : RawOriginal := C017.records[51]'(by decide)
theorem original_id2227 : original2227.index = 2227 := by decide

def c2227 : Contract := original2227.toContract.get (by decide)
theorem binding2227 : original2227.toContract = some c2227 := rfl

theorem checked2227 : check 4000 c2227 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2228 : RawOriginal := C017.records[52]'(by decide)
theorem original_id2228 : original2228.index = 2228 := by decide

def c2228 : Contract := original2228.toContract.get (by decide)
theorem binding2228 : original2228.toContract = some c2228 := rfl

theorem checked2228 : check 4000 c2228 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2229 : RawOriginal := C017.records[53]'(by decide)
theorem original_id2229 : original2229.index = 2229 := by decide

def c2229 : Contract := original2229.toContract.get (by decide)
theorem binding2229 : original2229.toContract = some c2229 := rfl

theorem checked2229 : check 4000 c2229 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2214, c2214, 4000, checked2214⟩,
  ⟨2215, c2215, 4000, checked2215⟩,
  ⟨2216, c2216, 4000, checked2216⟩,
  ⟨2217, c2217, 4000, checked2217⟩,
  ⟨2218, c2218, 4000, checked2218⟩,
  ⟨2219, c2219, 4000, checked2219⟩,
  ⟨2220, c2220, 4000, checked2220⟩,
  ⟨2221, c2221, 4000, checked2221⟩,
  ⟨2222, c2222, 4000, checked2222⟩,
  ⟨2223, c2223, 4000, checked2223⟩,
  ⟨2224, c2224, 4000, checked2224⟩,
  ⟨2225, c2225, 4000, checked2225⟩,
  ⟨2226, c2226, 4000, checked2226⟩,
  ⟨2227, c2227, 4000, checked2227⟩,
  ⟨2228, c2228, 4000, checked2228⟩,
  ⟨2229, c2229, 4000, checked2229⟩]

end PA215.ContractShards.Shard017Part2
