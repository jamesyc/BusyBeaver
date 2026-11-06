import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C033
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard033Part0
open PA215.Contracts PA215.Census

def original4230 : RawOriginal := C033.records[6]'(by decide)
theorem original_id4230 : original4230.index = 4230 := by decide

def c4230 : Contract := original4230.toContract.get (by decide)
theorem binding4230 : original4230.toContract = some c4230 := rfl

theorem checked4230 : check 4000 c4230 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4231 : RawOriginal := C033.records[7]'(by decide)
theorem original_id4231 : original4231.index = 4231 := by decide

def c4231 : Contract := original4231.toContract.get (by decide)
theorem binding4231 : original4231.toContract = some c4231 := rfl

theorem checked4231 : check 4000 c4231 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4232 : RawOriginal := C033.records[8]'(by decide)
theorem original_id4232 : original4232.index = 4232 := by decide

def c4232 : Contract := original4232.toContract.get (by decide)
theorem binding4232 : original4232.toContract = some c4232 := rfl

theorem checked4232 : check 4000 c4232 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4233 : RawOriginal := C033.records[9]'(by decide)
theorem original_id4233 : original4233.index = 4233 := by decide

def c4233 : Contract := original4233.toContract.get (by decide)
theorem binding4233 : original4233.toContract = some c4233 := rfl

theorem checked4233 : check 4000 c4233 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4234 : RawOriginal := C033.records[10]'(by decide)
theorem original_id4234 : original4234.index = 4234 := by decide

def c4234 : Contract := original4234.toContract.get (by decide)
theorem binding4234 : original4234.toContract = some c4234 := rfl

theorem checked4234 : check 4000 c4234 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4235 : RawOriginal := C033.records[11]'(by decide)
theorem original_id4235 : original4235.index = 4235 := by decide

def c4235 : Contract := original4235.toContract.get (by decide)
theorem binding4235 : original4235.toContract = some c4235 := rfl

theorem checked4235 : check 4000 c4235 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4236 : RawOriginal := C033.records[12]'(by decide)
theorem original_id4236 : original4236.index = 4236 := by decide

def c4236 : Contract := original4236.toContract.get (by decide)
theorem binding4236 : original4236.toContract = some c4236 := rfl

theorem checked4236 : check 4000 c4236 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4237 : RawOriginal := C033.records[13]'(by decide)
theorem original_id4237 : original4237.index = 4237 := by decide

def c4237 : Contract := original4237.toContract.get (by decide)
theorem binding4237 : original4237.toContract = some c4237 := rfl

theorem checked4237 : check 4000 c4237 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4238 : RawOriginal := C033.records[14]'(by decide)
theorem original_id4238 : original4238.index = 4238 := by decide

def c4238 : Contract := original4238.toContract.get (by decide)
theorem binding4238 : original4238.toContract = some c4238 := rfl

theorem checked4238 : check 4000 c4238 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4239 : RawOriginal := C033.records[15]'(by decide)
theorem original_id4239 : original4239.index = 4239 := by decide

def c4239 : Contract := original4239.toContract.get (by decide)
theorem binding4239 : original4239.toContract = some c4239 := rfl

theorem checked4239 : check 4000 c4239 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4240 : RawOriginal := C033.records[16]'(by decide)
theorem original_id4240 : original4240.index = 4240 := by decide

def c4240 : Contract := original4240.toContract.get (by decide)
theorem binding4240 : original4240.toContract = some c4240 := rfl

theorem checked4240 : check 4000 c4240 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4241 : RawOriginal := C033.records[17]'(by decide)
theorem original_id4241 : original4241.index = 4241 := by decide

def c4241 : Contract := original4241.toContract.get (by decide)
theorem binding4241 : original4241.toContract = some c4241 := rfl

theorem checked4241 : check 4000 c4241 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4242 : RawOriginal := C033.records[18]'(by decide)
theorem original_id4242 : original4242.index = 4242 := by decide

def c4242 : Contract := original4242.toContract.get (by decide)
theorem binding4242 : original4242.toContract = some c4242 := rfl

theorem checked4242 : check 4000 c4242 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4243 : RawOriginal := C033.records[19]'(by decide)
theorem original_id4243 : original4243.index = 4243 := by decide

def c4243 : Contract := original4243.toContract.get (by decide)
theorem binding4243 : original4243.toContract = some c4243 := rfl

theorem checked4243 : check 4000 c4243 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4244 : RawOriginal := C033.records[20]'(by decide)
theorem original_id4244 : original4244.index = 4244 := by decide

def c4244 : Contract := original4244.toContract.get (by decide)
theorem binding4244 : original4244.toContract = some c4244 := rfl

theorem checked4244 : check 4000 c4244 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4245 : RawOriginal := C033.records[21]'(by decide)
theorem original_id4245 : original4245.index = 4245 := by decide

def c4245 : Contract := original4245.toContract.get (by decide)
theorem binding4245 : original4245.toContract = some c4245 := rfl

theorem checked4245 : check 4000 c4245 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4230, c4230, 4000, checked4230⟩,
  ⟨4231, c4231, 4000, checked4231⟩,
  ⟨4232, c4232, 4000, checked4232⟩,
  ⟨4233, c4233, 4000, checked4233⟩,
  ⟨4234, c4234, 4000, checked4234⟩,
  ⟨4235, c4235, 4000, checked4235⟩,
  ⟨4236, c4236, 4000, checked4236⟩,
  ⟨4237, c4237, 4000, checked4237⟩,
  ⟨4238, c4238, 4000, checked4238⟩,
  ⟨4239, c4239, 4000, checked4239⟩,
  ⟨4240, c4240, 4000, checked4240⟩,
  ⟨4241, c4241, 4000, checked4241⟩,
  ⟨4242, c4242, 4000, checked4242⟩,
  ⟨4243, c4243, 4000, checked4243⟩,
  ⟨4244, c4244, 4000, checked4244⟩,
  ⟨4245, c4245, 4000, checked4245⟩]

end PA215.ContractShards.Shard033Part0
