import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C017
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard017Part0
open PA215.Contracts PA215.Census

def original2182 : RawOriginal := C017.records[6]'(by decide)
theorem original_id2182 : original2182.index = 2182 := by decide

def c2182 : Contract := original2182.toContract.get (by decide)
theorem binding2182 : original2182.toContract = some c2182 := rfl

theorem checked2182 : check 4000 c2182 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2183 : RawOriginal := C017.records[7]'(by decide)
theorem original_id2183 : original2183.index = 2183 := by decide

def c2183 : Contract := original2183.toContract.get (by decide)
theorem binding2183 : original2183.toContract = some c2183 := rfl

theorem checked2183 : check 4000 c2183 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2184 : RawOriginal := C017.records[8]'(by decide)
theorem original_id2184 : original2184.index = 2184 := by decide

def c2184 : Contract := original2184.toContract.get (by decide)
theorem binding2184 : original2184.toContract = some c2184 := rfl

theorem checked2184 : check 4000 c2184 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2185 : RawOriginal := C017.records[9]'(by decide)
theorem original_id2185 : original2185.index = 2185 := by decide

def c2185 : Contract := original2185.toContract.get (by decide)
theorem binding2185 : original2185.toContract = some c2185 := rfl

theorem checked2185 : check 4000 c2185 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2186 : RawOriginal := C017.records[10]'(by decide)
theorem original_id2186 : original2186.index = 2186 := by decide

def c2186 : Contract := original2186.toContract.get (by decide)
theorem binding2186 : original2186.toContract = some c2186 := rfl

theorem checked2186 : check 4000 c2186 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2187 : RawOriginal := C017.records[11]'(by decide)
theorem original_id2187 : original2187.index = 2187 := by decide

def c2187 : Contract := original2187.toContract.get (by decide)
theorem binding2187 : original2187.toContract = some c2187 := rfl

theorem checked2187 : check 4000 c2187 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2188 : RawOriginal := C017.records[12]'(by decide)
theorem original_id2188 : original2188.index = 2188 := by decide

def c2188 : Contract := original2188.toContract.get (by decide)
theorem binding2188 : original2188.toContract = some c2188 := rfl

theorem checked2188 : check 4000 c2188 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2189 : RawOriginal := C017.records[13]'(by decide)
theorem original_id2189 : original2189.index = 2189 := by decide

def c2189 : Contract := original2189.toContract.get (by decide)
theorem binding2189 : original2189.toContract = some c2189 := rfl

theorem checked2189 : check 4000 c2189 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2190 : RawOriginal := C017.records[14]'(by decide)
theorem original_id2190 : original2190.index = 2190 := by decide

def c2190 : Contract := original2190.toContract.get (by decide)
theorem binding2190 : original2190.toContract = some c2190 := rfl

theorem checked2190 : check 4000 c2190 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2191 : RawOriginal := C017.records[15]'(by decide)
theorem original_id2191 : original2191.index = 2191 := by decide

def c2191 : Contract := original2191.toContract.get (by decide)
theorem binding2191 : original2191.toContract = some c2191 := rfl

theorem checked2191 : check 4000 c2191 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2192 : RawOriginal := C017.records[16]'(by decide)
theorem original_id2192 : original2192.index = 2192 := by decide

def c2192 : Contract := original2192.toContract.get (by decide)
theorem binding2192 : original2192.toContract = some c2192 := rfl

theorem checked2192 : check 4000 c2192 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2193 : RawOriginal := C017.records[17]'(by decide)
theorem original_id2193 : original2193.index = 2193 := by decide

def c2193 : Contract := original2193.toContract.get (by decide)
theorem binding2193 : original2193.toContract = some c2193 := rfl

theorem checked2193 : check 4000 c2193 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2194 : RawOriginal := C017.records[18]'(by decide)
theorem original_id2194 : original2194.index = 2194 := by decide

def c2194 : Contract := original2194.toContract.get (by decide)
theorem binding2194 : original2194.toContract = some c2194 := rfl

theorem checked2194 : check 4000 c2194 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2195 : RawOriginal := C017.records[19]'(by decide)
theorem original_id2195 : original2195.index = 2195 := by decide

def c2195 : Contract := original2195.toContract.get (by decide)
theorem binding2195 : original2195.toContract = some c2195 := rfl

theorem checked2195 : check 4000 c2195 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2196 : RawOriginal := C017.records[20]'(by decide)
theorem original_id2196 : original2196.index = 2196 := by decide

def c2196 : Contract := original2196.toContract.get (by decide)
theorem binding2196 : original2196.toContract = some c2196 := rfl

theorem checked2196 : check 4000 c2196 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2197 : RawOriginal := C017.records[21]'(by decide)
theorem original_id2197 : original2197.index = 2197 := by decide

def c2197 : Contract := original2197.toContract.get (by decide)
theorem binding2197 : original2197.toContract = some c2197 := rfl

theorem checked2197 : check 4000 c2197 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2182, c2182, 4000, checked2182⟩,
  ⟨2183, c2183, 4000, checked2183⟩,
  ⟨2184, c2184, 4000, checked2184⟩,
  ⟨2185, c2185, 4000, checked2185⟩,
  ⟨2186, c2186, 4000, checked2186⟩,
  ⟨2187, c2187, 4000, checked2187⟩,
  ⟨2188, c2188, 4000, checked2188⟩,
  ⟨2189, c2189, 4000, checked2189⟩,
  ⟨2190, c2190, 4000, checked2190⟩,
  ⟨2191, c2191, 4000, checked2191⟩,
  ⟨2192, c2192, 4000, checked2192⟩,
  ⟨2193, c2193, 4000, checked2193⟩,
  ⟨2194, c2194, 4000, checked2194⟩,
  ⟨2195, c2195, 4000, checked2195⟩,
  ⟨2196, c2196, 4000, checked2196⟩,
  ⟨2197, c2197, 4000, checked2197⟩]

end PA215.ContractShards.Shard017Part0
