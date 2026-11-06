import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C031
import PA215.Census.C032
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard031Part7
open PA215.Contracts PA215.Census

def original4086 : RawOriginal := C031.records[118]'(by decide)
theorem original_id4086 : original4086.index = 4086 := by decide

def c4086 : Contract := original4086.toContract.get (by decide)
theorem binding4086 : original4086.toContract = some c4086 := rfl

theorem checked4086 : check 4000 c4086 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4087 : RawOriginal := C031.records[119]'(by decide)
theorem original_id4087 : original4087.index = 4087 := by decide

def c4087 : Contract := original4087.toContract.get (by decide)
theorem binding4087 : original4087.toContract = some c4087 := rfl

theorem checked4087 : check 4000 c4087 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4088 : RawOriginal := C031.records[120]'(by decide)
theorem original_id4088 : original4088.index = 4088 := by decide

def c4088 : Contract := original4088.toContract.get (by decide)
theorem binding4088 : original4088.toContract = some c4088 := rfl

theorem checked4088 : check 4000 c4088 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4089 : RawOriginal := C031.records[121]'(by decide)
theorem original_id4089 : original4089.index = 4089 := by decide

def c4089 : Contract := original4089.toContract.get (by decide)
theorem binding4089 : original4089.toContract = some c4089 := rfl

theorem checked4089 : check 4000 c4089 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4090 : RawOriginal := C031.records[122]'(by decide)
theorem original_id4090 : original4090.index = 4090 := by decide

def c4090 : Contract := original4090.toContract.get (by decide)
theorem binding4090 : original4090.toContract = some c4090 := rfl

theorem checked4090 : check 4000 c4090 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4091 : RawOriginal := C031.records[123]'(by decide)
theorem original_id4091 : original4091.index = 4091 := by decide

def c4091 : Contract := original4091.toContract.get (by decide)
theorem binding4091 : original4091.toContract = some c4091 := rfl

theorem checked4091 : check 4000 c4091 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4092 : RawOriginal := C031.records[124]'(by decide)
theorem original_id4092 : original4092.index = 4092 := by decide

def c4092 : Contract := original4092.toContract.get (by decide)
theorem binding4092 : original4092.toContract = some c4092 := rfl

theorem checked4092 : check 4000 c4092 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4093 : RawOriginal := C031.records[125]'(by decide)
theorem original_id4093 : original4093.index = 4093 := by decide

def c4093 : Contract := original4093.toContract.get (by decide)
theorem binding4093 : original4093.toContract = some c4093 := rfl

theorem checked4093 : check 4000 c4093 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4094 : RawOriginal := C031.records[126]'(by decide)
theorem original_id4094 : original4094.index = 4094 := by decide

def c4094 : Contract := original4094.toContract.get (by decide)
theorem binding4094 : original4094.toContract = some c4094 := rfl

theorem checked4094 : check 4000 c4094 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4095 : RawOriginal := C031.records[127]'(by decide)
theorem original_id4095 : original4095.index = 4095 := by decide

def c4095 : Contract := original4095.toContract.get (by decide)
theorem binding4095 : original4095.toContract = some c4095 := rfl

theorem checked4095 : check 4000 c4095 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4096 : RawOriginal := C032.records[0]'(by decide)
theorem original_id4096 : original4096.index = 4096 := by decide

def c4096 : Contract := original4096.toContract.get (by decide)
theorem binding4096 : original4096.toContract = some c4096 := rfl

theorem checked4096 : check 4000 c4096 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4097 : RawOriginal := C032.records[1]'(by decide)
theorem original_id4097 : original4097.index = 4097 := by decide

def c4097 : Contract := original4097.toContract.get (by decide)
theorem binding4097 : original4097.toContract = some c4097 := rfl

theorem checked4097 : check 4000 c4097 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4098 : RawOriginal := C032.records[2]'(by decide)
theorem original_id4098 : original4098.index = 4098 := by decide

def c4098 : Contract := original4098.toContract.get (by decide)
theorem binding4098 : original4098.toContract = some c4098 := rfl

theorem checked4098 : check 4000 c4098 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4099 : RawOriginal := C032.records[3]'(by decide)
theorem original_id4099 : original4099.index = 4099 := by decide

def c4099 : Contract := original4099.toContract.get (by decide)
theorem binding4099 : original4099.toContract = some c4099 := rfl

theorem checked4099 : check 4000 c4099 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4100 : RawOriginal := C032.records[4]'(by decide)
theorem original_id4100 : original4100.index = 4100 := by decide

def c4100 : Contract := original4100.toContract.get (by decide)
theorem binding4100 : original4100.toContract = some c4100 := rfl

theorem checked4100 : check 4000 c4100 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4101 : RawOriginal := C032.records[5]'(by decide)
theorem original_id4101 : original4101.index = 4101 := by decide

def c4101 : Contract := original4101.toContract.get (by decide)
theorem binding4101 : original4101.toContract = some c4101 := rfl

theorem checked4101 : check 4000 c4101 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4086, c4086, 4000, checked4086⟩,
  ⟨4087, c4087, 4000, checked4087⟩,
  ⟨4088, c4088, 4000, checked4088⟩,
  ⟨4089, c4089, 4000, checked4089⟩,
  ⟨4090, c4090, 4000, checked4090⟩,
  ⟨4091, c4091, 4000, checked4091⟩,
  ⟨4092, c4092, 4000, checked4092⟩,
  ⟨4093, c4093, 4000, checked4093⟩,
  ⟨4094, c4094, 4000, checked4094⟩,
  ⟨4095, c4095, 4000, checked4095⟩,
  ⟨4096, c4096, 4000, checked4096⟩,
  ⟨4097, c4097, 4000, checked4097⟩,
  ⟨4098, c4098, 4000, checked4098⟩,
  ⟨4099, c4099, 4000, checked4099⟩,
  ⟨4100, c4100, 4000, checked4100⟩,
  ⟨4101, c4101, 4000, checked4101⟩]

end PA215.ContractShards.Shard031Part7
