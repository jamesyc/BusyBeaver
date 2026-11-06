import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C032
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard032Part0
open PA215.Contracts PA215.Census

def original4102 : RawOriginal := C032.records[6]'(by decide)
theorem original_id4102 : original4102.index = 4102 := by decide

def c4102 : Contract := original4102.toContract.get (by decide)
theorem binding4102 : original4102.toContract = some c4102 := rfl

theorem checked4102 : check 4000 c4102 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4103 : RawOriginal := C032.records[7]'(by decide)
theorem original_id4103 : original4103.index = 4103 := by decide

def c4103 : Contract := original4103.toContract.get (by decide)
theorem binding4103 : original4103.toContract = some c4103 := rfl

theorem checked4103 : check 4000 c4103 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4104 : RawOriginal := C032.records[8]'(by decide)
theorem original_id4104 : original4104.index = 4104 := by decide

def c4104 : Contract := original4104.toContract.get (by decide)
theorem binding4104 : original4104.toContract = some c4104 := rfl

theorem checked4104 : check 4000 c4104 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4105 : RawOriginal := C032.records[9]'(by decide)
theorem original_id4105 : original4105.index = 4105 := by decide

def c4105 : Contract := original4105.toContract.get (by decide)
theorem binding4105 : original4105.toContract = some c4105 := rfl

theorem checked4105 : check 4000 c4105 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4106 : RawOriginal := C032.records[10]'(by decide)
theorem original_id4106 : original4106.index = 4106 := by decide

def c4106 : Contract := original4106.toContract.get (by decide)
theorem binding4106 : original4106.toContract = some c4106 := rfl

theorem checked4106 : check 4000 c4106 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4107 : RawOriginal := C032.records[11]'(by decide)
theorem original_id4107 : original4107.index = 4107 := by decide

def c4107 : Contract := original4107.toContract.get (by decide)
theorem binding4107 : original4107.toContract = some c4107 := rfl

theorem checked4107 : check 4000 c4107 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4108 : RawOriginal := C032.records[12]'(by decide)
theorem original_id4108 : original4108.index = 4108 := by decide

def c4108 : Contract := original4108.toContract.get (by decide)
theorem binding4108 : original4108.toContract = some c4108 := rfl

theorem checked4108 : check 4000 c4108 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4109 : RawOriginal := C032.records[13]'(by decide)
theorem original_id4109 : original4109.index = 4109 := by decide

def c4109 : Contract := original4109.toContract.get (by decide)
theorem binding4109 : original4109.toContract = some c4109 := rfl

theorem checked4109 : check 4000 c4109 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4110 : RawOriginal := C032.records[14]'(by decide)
theorem original_id4110 : original4110.index = 4110 := by decide

def c4110 : Contract := original4110.toContract.get (by decide)
theorem binding4110 : original4110.toContract = some c4110 := rfl

theorem checked4110 : check 4000 c4110 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4111 : RawOriginal := C032.records[15]'(by decide)
theorem original_id4111 : original4111.index = 4111 := by decide

def c4111 : Contract := original4111.toContract.get (by decide)
theorem binding4111 : original4111.toContract = some c4111 := rfl

theorem checked4111 : check 4000 c4111 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4112 : RawOriginal := C032.records[16]'(by decide)
theorem original_id4112 : original4112.index = 4112 := by decide

def c4112 : Contract := original4112.toContract.get (by decide)
theorem binding4112 : original4112.toContract = some c4112 := rfl

theorem checked4112 : check 4000 c4112 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4113 : RawOriginal := C032.records[17]'(by decide)
theorem original_id4113 : original4113.index = 4113 := by decide

def c4113 : Contract := original4113.toContract.get (by decide)
theorem binding4113 : original4113.toContract = some c4113 := rfl

theorem checked4113 : check 4000 c4113 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4114 : RawOriginal := C032.records[18]'(by decide)
theorem original_id4114 : original4114.index = 4114 := by decide

def c4114 : Contract := original4114.toContract.get (by decide)
theorem binding4114 : original4114.toContract = some c4114 := rfl

theorem checked4114 : check 4000 c4114 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4115 : RawOriginal := C032.records[19]'(by decide)
theorem original_id4115 : original4115.index = 4115 := by decide

def c4115 : Contract := original4115.toContract.get (by decide)
theorem binding4115 : original4115.toContract = some c4115 := rfl

theorem checked4115 : check 4000 c4115 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4116 : RawOriginal := C032.records[20]'(by decide)
theorem original_id4116 : original4116.index = 4116 := by decide

def c4116 : Contract := original4116.toContract.get (by decide)
theorem binding4116 : original4116.toContract = some c4116 := rfl

theorem checked4116 : check 4000 c4116 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4117 : RawOriginal := C032.records[21]'(by decide)
theorem original_id4117 : original4117.index = 4117 := by decide

def c4117 : Contract := original4117.toContract.get (by decide)
theorem binding4117 : original4117.toContract = some c4117 := rfl

theorem checked4117 : check 4000 c4117 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4102, c4102, 4000, checked4102⟩,
  ⟨4103, c4103, 4000, checked4103⟩,
  ⟨4104, c4104, 4000, checked4104⟩,
  ⟨4105, c4105, 4000, checked4105⟩,
  ⟨4106, c4106, 4000, checked4106⟩,
  ⟨4107, c4107, 4000, checked4107⟩,
  ⟨4108, c4108, 4000, checked4108⟩,
  ⟨4109, c4109, 4000, checked4109⟩,
  ⟨4110, c4110, 4000, checked4110⟩,
  ⟨4111, c4111, 4000, checked4111⟩,
  ⟨4112, c4112, 4000, checked4112⟩,
  ⟨4113, c4113, 4000, checked4113⟩,
  ⟨4114, c4114, 4000, checked4114⟩,
  ⟨4115, c4115, 4000, checked4115⟩,
  ⟨4116, c4116, 4000, checked4116⟩,
  ⟨4117, c4117, 4000, checked4117⟩]

end PA215.ContractShards.Shard032Part0
