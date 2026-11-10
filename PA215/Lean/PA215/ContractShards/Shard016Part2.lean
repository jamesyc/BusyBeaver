import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C016
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard016Part2
open PA215.Contracts PA215.Census

def original2086 : RawOriginal := C016.records[38]'(by decide)
theorem original_id2086 : original2086.index = 2086 := by decide

def c2086 : Contract := original2086.toContract.get (by decide)
theorem binding2086 : original2086.toContract = some c2086 := rfl

theorem checked2086 : check 4000 c2086 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2087 : RawOriginal := C016.records[39]'(by decide)
theorem original_id2087 : original2087.index = 2087 := by decide

def c2087 : Contract := original2087.toContract.get (by decide)
theorem binding2087 : original2087.toContract = some c2087 := rfl

theorem checked2087 : check 4000 c2087 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2088 : RawOriginal := C016.records[40]'(by decide)
theorem original_id2088 : original2088.index = 2088 := by decide

def c2088 : Contract := original2088.toContract.get (by decide)
theorem binding2088 : original2088.toContract = some c2088 := rfl

theorem checked2088 : check 4000 c2088 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2089 : RawOriginal := C016.records[41]'(by decide)
theorem original_id2089 : original2089.index = 2089 := by decide

def c2089 : Contract := original2089.toContract.get (by decide)
theorem binding2089 : original2089.toContract = some c2089 := rfl

theorem checked2089 : check 4000 c2089 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2090 : RawOriginal := C016.records[42]'(by decide)
theorem original_id2090 : original2090.index = 2090 := by decide

def c2090 : Contract := original2090.toContract.get (by decide)
theorem binding2090 : original2090.toContract = some c2090 := rfl

theorem checked2090 : check 4000 c2090 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2091 : RawOriginal := C016.records[43]'(by decide)
theorem original_id2091 : original2091.index = 2091 := by decide

def c2091 : Contract := original2091.toContract.get (by decide)
theorem binding2091 : original2091.toContract = some c2091 := rfl

theorem checked2091 : check 4000 c2091 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2092 : RawOriginal := C016.records[44]'(by decide)
theorem original_id2092 : original2092.index = 2092 := by decide

def c2092 : Contract := original2092.toContract.get (by decide)
theorem binding2092 : original2092.toContract = some c2092 := rfl

theorem checked2092 : check 4000 c2092 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2093 : RawOriginal := C016.records[45]'(by decide)
theorem original_id2093 : original2093.index = 2093 := by decide

def c2093 : Contract := original2093.toContract.get (by decide)
theorem binding2093 : original2093.toContract = some c2093 := rfl

theorem checked2093 : check 4000 c2093 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2094 : RawOriginal := C016.records[46]'(by decide)
theorem original_id2094 : original2094.index = 2094 := by decide

def c2094 : Contract := original2094.toContract.get (by decide)
theorem binding2094 : original2094.toContract = some c2094 := rfl

theorem checked2094 : check 4000 c2094 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2095 : RawOriginal := C016.records[47]'(by decide)
theorem original_id2095 : original2095.index = 2095 := by decide

def c2095 : Contract := original2095.toContract.get (by decide)
theorem binding2095 : original2095.toContract = some c2095 := rfl

theorem checked2095 : check 4000 c2095 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2096 : RawOriginal := C016.records[48]'(by decide)
theorem original_id2096 : original2096.index = 2096 := by decide

def c2096 : Contract := original2096.toContract.get (by decide)
theorem binding2096 : original2096.toContract = some c2096 := rfl

theorem checked2096 : check 4000 c2096 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2097 : RawOriginal := C016.records[49]'(by decide)
theorem original_id2097 : original2097.index = 2097 := by decide

def c2097 : Contract := original2097.toContract.get (by decide)
theorem binding2097 : original2097.toContract = some c2097 := rfl

theorem checked2097 : check 4000 c2097 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2098 : RawOriginal := C016.records[50]'(by decide)
theorem original_id2098 : original2098.index = 2098 := by decide

def c2098 : Contract := original2098.toContract.get (by decide)
theorem binding2098 : original2098.toContract = some c2098 := rfl

theorem checked2098 : check 4000 c2098 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2099 : RawOriginal := C016.records[51]'(by decide)
theorem original_id2099 : original2099.index = 2099 := by decide

def c2099 : Contract := original2099.toContract.get (by decide)
theorem binding2099 : original2099.toContract = some c2099 := rfl

theorem checked2099 : check 4000 c2099 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2100 : RawOriginal := C016.records[52]'(by decide)
theorem original_id2100 : original2100.index = 2100 := by decide

def c2100 : Contract := original2100.toContract.get (by decide)
theorem binding2100 : original2100.toContract = some c2100 := rfl

theorem checked2100 : check 4000 c2100 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2101 : RawOriginal := C016.records[53]'(by decide)
theorem original_id2101 : original2101.index = 2101 := by decide

def c2101 : Contract := original2101.toContract.get (by decide)
theorem binding2101 : original2101.toContract = some c2101 := rfl

theorem checked2101 : check 4000 c2101 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2086, c2086, 4000, checked2086⟩,
  ⟨2087, c2087, 4000, checked2087⟩,
  ⟨2088, c2088, 4000, checked2088⟩,
  ⟨2089, c2089, 4000, checked2089⟩,
  ⟨2090, c2090, 4000, checked2090⟩,
  ⟨2091, c2091, 4000, checked2091⟩,
  ⟨2092, c2092, 4000, checked2092⟩,
  ⟨2093, c2093, 4000, checked2093⟩,
  ⟨2094, c2094, 4000, checked2094⟩,
  ⟨2095, c2095, 4000, checked2095⟩,
  ⟨2096, c2096, 4000, checked2096⟩,
  ⟨2097, c2097, 4000, checked2097⟩,
  ⟨2098, c2098, 4000, checked2098⟩,
  ⟨2099, c2099, 4000, checked2099⟩,
  ⟨2100, c2100, 4000, checked2100⟩,
  ⟨2101, c2101, 4000, checked2101⟩]

end PA215.ContractShards.Shard016Part2
