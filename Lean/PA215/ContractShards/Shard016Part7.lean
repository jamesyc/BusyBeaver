import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C016
import PA215.Census.C017
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard016Part7
open PA215.Contracts PA215.Census

def original2166 : RawOriginal := C016.records[118]'(by decide)
theorem original_id2166 : original2166.index = 2166 := by decide

def c2166 : Contract := original2166.toContract.get (by decide)
theorem binding2166 : original2166.toContract = some c2166 := rfl

theorem checked2166 : check 4000 c2166 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2167 : RawOriginal := C016.records[119]'(by decide)
theorem original_id2167 : original2167.index = 2167 := by decide

def c2167 : Contract := original2167.toContract.get (by decide)
theorem binding2167 : original2167.toContract = some c2167 := rfl

theorem checked2167 : check 4000 c2167 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2168 : RawOriginal := C016.records[120]'(by decide)
theorem original_id2168 : original2168.index = 2168 := by decide

def c2168 : Contract := original2168.toContract.get (by decide)
theorem binding2168 : original2168.toContract = some c2168 := rfl

theorem checked2168 : check 4000 c2168 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2169 : RawOriginal := C016.records[121]'(by decide)
theorem original_id2169 : original2169.index = 2169 := by decide

def c2169 : Contract := original2169.toContract.get (by decide)
theorem binding2169 : original2169.toContract = some c2169 := rfl

theorem checked2169 : check 4000 c2169 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2170 : RawOriginal := C016.records[122]'(by decide)
theorem original_id2170 : original2170.index = 2170 := by decide

def c2170 : Contract := original2170.toContract.get (by decide)
theorem binding2170 : original2170.toContract = some c2170 := rfl

theorem checked2170 : check 4000 c2170 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2171 : RawOriginal := C016.records[123]'(by decide)
theorem original_id2171 : original2171.index = 2171 := by decide

def c2171 : Contract := original2171.toContract.get (by decide)
theorem binding2171 : original2171.toContract = some c2171 := rfl

theorem checked2171 : check 4000 c2171 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2172 : RawOriginal := C016.records[124]'(by decide)
theorem original_id2172 : original2172.index = 2172 := by decide

def c2172 : Contract := original2172.toContract.get (by decide)
theorem binding2172 : original2172.toContract = some c2172 := rfl

theorem checked2172 : check 4000 c2172 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2173 : RawOriginal := C016.records[125]'(by decide)
theorem original_id2173 : original2173.index = 2173 := by decide

def c2173 : Contract := original2173.toContract.get (by decide)
theorem binding2173 : original2173.toContract = some c2173 := rfl

theorem checked2173 : check 4000 c2173 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2174 : RawOriginal := C016.records[126]'(by decide)
theorem original_id2174 : original2174.index = 2174 := by decide

def c2174 : Contract := original2174.toContract.get (by decide)
theorem binding2174 : original2174.toContract = some c2174 := rfl

theorem checked2174 : check 4000 c2174 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2175 : RawOriginal := C016.records[127]'(by decide)
theorem original_id2175 : original2175.index = 2175 := by decide

def c2175 : Contract := original2175.toContract.get (by decide)
theorem binding2175 : original2175.toContract = some c2175 := rfl

theorem checked2175 : check 4000 c2175 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2176 : RawOriginal := C017.records[0]'(by decide)
theorem original_id2176 : original2176.index = 2176 := by decide

def c2176 : Contract := original2176.toContract.get (by decide)
theorem binding2176 : original2176.toContract = some c2176 := rfl

theorem checked2176 : check 4000 c2176 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2177 : RawOriginal := C017.records[1]'(by decide)
theorem original_id2177 : original2177.index = 2177 := by decide

def c2177 : Contract := original2177.toContract.get (by decide)
theorem binding2177 : original2177.toContract = some c2177 := rfl

theorem checked2177 : check 4000 c2177 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2178 : RawOriginal := C017.records[2]'(by decide)
theorem original_id2178 : original2178.index = 2178 := by decide

def c2178 : Contract := original2178.toContract.get (by decide)
theorem binding2178 : original2178.toContract = some c2178 := rfl

theorem checked2178 : check 4000 c2178 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2179 : RawOriginal := C017.records[3]'(by decide)
theorem original_id2179 : original2179.index = 2179 := by decide

def c2179 : Contract := original2179.toContract.get (by decide)
theorem binding2179 : original2179.toContract = some c2179 := rfl

theorem checked2179 : check 4000 c2179 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2180 : RawOriginal := C017.records[4]'(by decide)
theorem original_id2180 : original2180.index = 2180 := by decide

def c2180 : Contract := original2180.toContract.get (by decide)
theorem binding2180 : original2180.toContract = some c2180 := rfl

theorem checked2180 : check 4000 c2180 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2181 : RawOriginal := C017.records[5]'(by decide)
theorem original_id2181 : original2181.index = 2181 := by decide

def c2181 : Contract := original2181.toContract.get (by decide)
theorem binding2181 : original2181.toContract = some c2181 := rfl

theorem checked2181 : check 4000 c2181 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2166, c2166, 4000, checked2166⟩,
  ⟨2167, c2167, 4000, checked2167⟩,
  ⟨2168, c2168, 4000, checked2168⟩,
  ⟨2169, c2169, 4000, checked2169⟩,
  ⟨2170, c2170, 4000, checked2170⟩,
  ⟨2171, c2171, 4000, checked2171⟩,
  ⟨2172, c2172, 4000, checked2172⟩,
  ⟨2173, c2173, 4000, checked2173⟩,
  ⟨2174, c2174, 4000, checked2174⟩,
  ⟨2175, c2175, 4000, checked2175⟩,
  ⟨2176, c2176, 4000, checked2176⟩,
  ⟨2177, c2177, 4000, checked2177⟩,
  ⟨2178, c2178, 4000, checked2178⟩,
  ⟨2179, c2179, 4000, checked2179⟩,
  ⟨2180, c2180, 4000, checked2180⟩,
  ⟨2181, c2181, 4000, checked2181⟩]

end PA215.ContractShards.Shard016Part7
