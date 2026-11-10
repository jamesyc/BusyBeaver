import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C039
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard039Part5
open PA215.Contracts PA215.Census

def original5079 : RawOriginal := C039.records[87]'(by decide)
theorem original_id5079 : original5079.index = 5079 := by decide

def c5079 : Contract := original5079.toContract.get (by decide)
theorem binding5079 : original5079.toContract = some c5079 := rfl

theorem checked5079 : check 4000 c5079 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5080 : RawOriginal := C039.records[88]'(by decide)
theorem original_id5080 : original5080.index = 5080 := by decide

def c5080 : Contract := original5080.toContract.get (by decide)
theorem binding5080 : original5080.toContract = some c5080 := rfl

theorem checked5080 : check 4000 c5080 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5081 : RawOriginal := C039.records[89]'(by decide)
theorem original_id5081 : original5081.index = 5081 := by decide

def c5081 : Contract := original5081.toContract.get (by decide)
theorem binding5081 : original5081.toContract = some c5081 := rfl

theorem checked5081 : check 4000 c5081 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5082 : RawOriginal := C039.records[90]'(by decide)
theorem original_id5082 : original5082.index = 5082 := by decide

def c5082 : Contract := original5082.toContract.get (by decide)
theorem binding5082 : original5082.toContract = some c5082 := rfl

theorem checked5082 : check 4000 c5082 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5083 : RawOriginal := C039.records[91]'(by decide)
theorem original_id5083 : original5083.index = 5083 := by decide

def c5083 : Contract := original5083.toContract.get (by decide)
theorem binding5083 : original5083.toContract = some c5083 := rfl

theorem checked5083 : check 4000 c5083 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5089 : RawOriginal := C039.records[97]'(by decide)
theorem original_id5089 : original5089.index = 5089 := by decide

def c5089 : Contract := original5089.toContract.get (by decide)
theorem binding5089 : original5089.toContract = some c5089 := rfl

theorem checked5089 : check 4000 c5089 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5090 : RawOriginal := C039.records[98]'(by decide)
theorem original_id5090 : original5090.index = 5090 := by decide

def c5090 : Contract := original5090.toContract.get (by decide)
theorem binding5090 : original5090.toContract = some c5090 := rfl

theorem checked5090 : check 4000 c5090 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5091 : RawOriginal := C039.records[99]'(by decide)
theorem original_id5091 : original5091.index = 5091 := by decide

def c5091 : Contract := original5091.toContract.get (by decide)
theorem binding5091 : original5091.toContract = some c5091 := rfl

theorem checked5091 : check 4000 c5091 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5092 : RawOriginal := C039.records[100]'(by decide)
theorem original_id5092 : original5092.index = 5092 := by decide

def c5092 : Contract := original5092.toContract.get (by decide)
theorem binding5092 : original5092.toContract = some c5092 := rfl

theorem checked5092 : check 4000 c5092 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5093 : RawOriginal := C039.records[101]'(by decide)
theorem original_id5093 : original5093.index = 5093 := by decide

def c5093 : Contract := original5093.toContract.get (by decide)
theorem binding5093 : original5093.toContract = some c5093 := rfl

theorem checked5093 : check 4000 c5093 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5094 : RawOriginal := C039.records[102]'(by decide)
theorem original_id5094 : original5094.index = 5094 := by decide

def c5094 : Contract := original5094.toContract.get (by decide)
theorem binding5094 : original5094.toContract = some c5094 := rfl

theorem checked5094 : check 4000 c5094 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5095 : RawOriginal := C039.records[103]'(by decide)
theorem original_id5095 : original5095.index = 5095 := by decide

def c5095 : Contract := original5095.toContract.get (by decide)
theorem binding5095 : original5095.toContract = some c5095 := rfl

theorem checked5095 : check 4000 c5095 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5096 : RawOriginal := C039.records[104]'(by decide)
theorem original_id5096 : original5096.index = 5096 := by decide

def c5096 : Contract := original5096.toContract.get (by decide)
theorem binding5096 : original5096.toContract = some c5096 := rfl

theorem checked5096 : check 4000 c5096 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5097 : RawOriginal := C039.records[105]'(by decide)
theorem original_id5097 : original5097.index = 5097 := by decide

def c5097 : Contract := original5097.toContract.get (by decide)
theorem binding5097 : original5097.toContract = some c5097 := rfl

theorem checked5097 : check 4000 c5097 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5098 : RawOriginal := C039.records[106]'(by decide)
theorem original_id5098 : original5098.index = 5098 := by decide

def c5098 : Contract := original5098.toContract.get (by decide)
theorem binding5098 : original5098.toContract = some c5098 := rfl

theorem checked5098 : check 4000 c5098 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5099 : RawOriginal := C039.records[107]'(by decide)
theorem original_id5099 : original5099.index = 5099 := by decide

def c5099 : Contract := original5099.toContract.get (by decide)
theorem binding5099 : original5099.toContract = some c5099 := rfl

theorem checked5099 : check 4000 c5099 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨5079, c5079, 4000, checked5079⟩,
  ⟨5080, c5080, 4000, checked5080⟩,
  ⟨5081, c5081, 4000, checked5081⟩,
  ⟨5082, c5082, 4000, checked5082⟩,
  ⟨5083, c5083, 4000, checked5083⟩,
  ⟨5089, c5089, 4000, checked5089⟩,
  ⟨5090, c5090, 4000, checked5090⟩,
  ⟨5091, c5091, 4000, checked5091⟩,
  ⟨5092, c5092, 4000, checked5092⟩,
  ⟨5093, c5093, 4000, checked5093⟩,
  ⟨5094, c5094, 4000, checked5094⟩,
  ⟨5095, c5095, 4000, checked5095⟩,
  ⟨5096, c5096, 4000, checked5096⟩,
  ⟨5097, c5097, 4000, checked5097⟩,
  ⟨5098, c5098, 4000, checked5098⟩,
  ⟨5099, c5099, 4000, checked5099⟩]

end PA215.ContractShards.Shard039Part5
