import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C032
import PA215.Census.C033
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard032Part7
open PA215.Contracts PA215.Census

def original4214 : RawOriginal := C032.records[118]'(by decide)
theorem original_id4214 : original4214.index = 4214 := by decide

def c4214 : Contract := original4214.toContract.get (by decide)
theorem binding4214 : original4214.toContract = some c4214 := rfl

theorem checked4214 : check 4000 c4214 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4215 : RawOriginal := C032.records[119]'(by decide)
theorem original_id4215 : original4215.index = 4215 := by decide

def c4215 : Contract := original4215.toContract.get (by decide)
theorem binding4215 : original4215.toContract = some c4215 := rfl

theorem checked4215 : check 4000 c4215 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4216 : RawOriginal := C032.records[120]'(by decide)
theorem original_id4216 : original4216.index = 4216 := by decide

def c4216 : Contract := original4216.toContract.get (by decide)
theorem binding4216 : original4216.toContract = some c4216 := rfl

theorem checked4216 : check 4000 c4216 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4217 : RawOriginal := C032.records[121]'(by decide)
theorem original_id4217 : original4217.index = 4217 := by decide

def c4217 : Contract := original4217.toContract.get (by decide)
theorem binding4217 : original4217.toContract = some c4217 := rfl

theorem checked4217 : check 4000 c4217 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4218 : RawOriginal := C032.records[122]'(by decide)
theorem original_id4218 : original4218.index = 4218 := by decide

def c4218 : Contract := original4218.toContract.get (by decide)
theorem binding4218 : original4218.toContract = some c4218 := rfl

theorem checked4218 : check 4000 c4218 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4219 : RawOriginal := C032.records[123]'(by decide)
theorem original_id4219 : original4219.index = 4219 := by decide

def c4219 : Contract := original4219.toContract.get (by decide)
theorem binding4219 : original4219.toContract = some c4219 := rfl

theorem checked4219 : check 4000 c4219 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4220 : RawOriginal := C032.records[124]'(by decide)
theorem original_id4220 : original4220.index = 4220 := by decide

def c4220 : Contract := original4220.toContract.get (by decide)
theorem binding4220 : original4220.toContract = some c4220 := rfl

theorem checked4220 : check 4000 c4220 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4221 : RawOriginal := C032.records[125]'(by decide)
theorem original_id4221 : original4221.index = 4221 := by decide

def c4221 : Contract := original4221.toContract.get (by decide)
theorem binding4221 : original4221.toContract = some c4221 := rfl

theorem checked4221 : check 4000 c4221 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4222 : RawOriginal := C032.records[126]'(by decide)
theorem original_id4222 : original4222.index = 4222 := by decide

def c4222 : Contract := original4222.toContract.get (by decide)
theorem binding4222 : original4222.toContract = some c4222 := rfl

theorem checked4222 : check 4000 c4222 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4223 : RawOriginal := C032.records[127]'(by decide)
theorem original_id4223 : original4223.index = 4223 := by decide

def c4223 : Contract := original4223.toContract.get (by decide)
theorem binding4223 : original4223.toContract = some c4223 := rfl

theorem checked4223 : check 4000 c4223 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4224 : RawOriginal := C033.records[0]'(by decide)
theorem original_id4224 : original4224.index = 4224 := by decide

def c4224 : Contract := original4224.toContract.get (by decide)
theorem binding4224 : original4224.toContract = some c4224 := rfl

theorem checked4224 : check 4000 c4224 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4225 : RawOriginal := C033.records[1]'(by decide)
theorem original_id4225 : original4225.index = 4225 := by decide

def c4225 : Contract := original4225.toContract.get (by decide)
theorem binding4225 : original4225.toContract = some c4225 := rfl

theorem checked4225 : check 4000 c4225 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4226 : RawOriginal := C033.records[2]'(by decide)
theorem original_id4226 : original4226.index = 4226 := by decide

def c4226 : Contract := original4226.toContract.get (by decide)
theorem binding4226 : original4226.toContract = some c4226 := rfl

theorem checked4226 : check 4000 c4226 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4227 : RawOriginal := C033.records[3]'(by decide)
theorem original_id4227 : original4227.index = 4227 := by decide

def c4227 : Contract := original4227.toContract.get (by decide)
theorem binding4227 : original4227.toContract = some c4227 := rfl

theorem checked4227 : check 4000 c4227 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4228 : RawOriginal := C033.records[4]'(by decide)
theorem original_id4228 : original4228.index = 4228 := by decide

def c4228 : Contract := original4228.toContract.get (by decide)
theorem binding4228 : original4228.toContract = some c4228 := rfl

theorem checked4228 : check 4000 c4228 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4229 : RawOriginal := C033.records[5]'(by decide)
theorem original_id4229 : original4229.index = 4229 := by decide

def c4229 : Contract := original4229.toContract.get (by decide)
theorem binding4229 : original4229.toContract = some c4229 := rfl

theorem checked4229 : check 4000 c4229 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4214, c4214, 4000, checked4214⟩,
  ⟨4215, c4215, 4000, checked4215⟩,
  ⟨4216, c4216, 4000, checked4216⟩,
  ⟨4217, c4217, 4000, checked4217⟩,
  ⟨4218, c4218, 4000, checked4218⟩,
  ⟨4219, c4219, 4000, checked4219⟩,
  ⟨4220, c4220, 4000, checked4220⟩,
  ⟨4221, c4221, 4000, checked4221⟩,
  ⟨4222, c4222, 4000, checked4222⟩,
  ⟨4223, c4223, 4000, checked4223⟩,
  ⟨4224, c4224, 4000, checked4224⟩,
  ⟨4225, c4225, 4000, checked4225⟩,
  ⟨4226, c4226, 4000, checked4226⟩,
  ⟨4227, c4227, 4000, checked4227⟩,
  ⟨4228, c4228, 4000, checked4228⟩,
  ⟨4229, c4229, 4000, checked4229⟩]

end PA215.ContractShards.Shard032Part7
