import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C033
import PA215.Census.C034
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard033Part7
open PA215.Contracts PA215.Census

def original4342 : RawOriginal := C033.records[118]'(by decide)
theorem original_id4342 : original4342.index = 4342 := by decide

def c4342 : Contract := original4342.toContract.get (by decide)
theorem binding4342 : original4342.toContract = some c4342 := rfl

theorem checked4342 : check 4000 c4342 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4343 : RawOriginal := C033.records[119]'(by decide)
theorem original_id4343 : original4343.index = 4343 := by decide

def c4343 : Contract := original4343.toContract.get (by decide)
theorem binding4343 : original4343.toContract = some c4343 := rfl

theorem checked4343 : check 4000 c4343 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4344 : RawOriginal := C033.records[120]'(by decide)
theorem original_id4344 : original4344.index = 4344 := by decide

def c4344 : Contract := original4344.toContract.get (by decide)
theorem binding4344 : original4344.toContract = some c4344 := rfl

theorem checked4344 : check 4000 c4344 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4345 : RawOriginal := C033.records[121]'(by decide)
theorem original_id4345 : original4345.index = 4345 := by decide

def c4345 : Contract := original4345.toContract.get (by decide)
theorem binding4345 : original4345.toContract = some c4345 := rfl

theorem checked4345 : check 4000 c4345 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4346 : RawOriginal := C033.records[122]'(by decide)
theorem original_id4346 : original4346.index = 4346 := by decide

def c4346 : Contract := original4346.toContract.get (by decide)
theorem binding4346 : original4346.toContract = some c4346 := rfl

theorem checked4346 : check 4000 c4346 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4347 : RawOriginal := C033.records[123]'(by decide)
theorem original_id4347 : original4347.index = 4347 := by decide

def c4347 : Contract := original4347.toContract.get (by decide)
theorem binding4347 : original4347.toContract = some c4347 := rfl

theorem checked4347 : check 4000 c4347 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4348 : RawOriginal := C033.records[124]'(by decide)
theorem original_id4348 : original4348.index = 4348 := by decide

def c4348 : Contract := original4348.toContract.get (by decide)
theorem binding4348 : original4348.toContract = some c4348 := rfl

theorem checked4348 : check 4000 c4348 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4349 : RawOriginal := C033.records[125]'(by decide)
theorem original_id4349 : original4349.index = 4349 := by decide

def c4349 : Contract := original4349.toContract.get (by decide)
theorem binding4349 : original4349.toContract = some c4349 := rfl

theorem checked4349 : check 4000 c4349 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4350 : RawOriginal := C033.records[126]'(by decide)
theorem original_id4350 : original4350.index = 4350 := by decide

def c4350 : Contract := original4350.toContract.get (by decide)
theorem binding4350 : original4350.toContract = some c4350 := rfl

theorem checked4350 : check 4000 c4350 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4351 : RawOriginal := C033.records[127]'(by decide)
theorem original_id4351 : original4351.index = 4351 := by decide

def c4351 : Contract := original4351.toContract.get (by decide)
theorem binding4351 : original4351.toContract = some c4351 := rfl

theorem checked4351 : check 4000 c4351 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4352 : RawOriginal := C034.records[0]'(by decide)
theorem original_id4352 : original4352.index = 4352 := by decide

def c4352 : Contract := original4352.toContract.get (by decide)
theorem binding4352 : original4352.toContract = some c4352 := rfl

theorem checked4352 : check 4000 c4352 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4353 : RawOriginal := C034.records[1]'(by decide)
theorem original_id4353 : original4353.index = 4353 := by decide

def c4353 : Contract := original4353.toContract.get (by decide)
theorem binding4353 : original4353.toContract = some c4353 := rfl

theorem checked4353 : check 4000 c4353 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4354 : RawOriginal := C034.records[2]'(by decide)
theorem original_id4354 : original4354.index = 4354 := by decide

def c4354 : Contract := original4354.toContract.get (by decide)
theorem binding4354 : original4354.toContract = some c4354 := rfl

theorem checked4354 : check 4000 c4354 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4355 : RawOriginal := C034.records[3]'(by decide)
theorem original_id4355 : original4355.index = 4355 := by decide

def c4355 : Contract := original4355.toContract.get (by decide)
theorem binding4355 : original4355.toContract = some c4355 := rfl

theorem checked4355 : check 4000 c4355 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4356 : RawOriginal := C034.records[4]'(by decide)
theorem original_id4356 : original4356.index = 4356 := by decide

def c4356 : Contract := original4356.toContract.get (by decide)
theorem binding4356 : original4356.toContract = some c4356 := rfl

theorem checked4356 : check 4000 c4356 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4357 : RawOriginal := C034.records[5]'(by decide)
theorem original_id4357 : original4357.index = 4357 := by decide

def c4357 : Contract := original4357.toContract.get (by decide)
theorem binding4357 : original4357.toContract = some c4357 := rfl

theorem checked4357 : check 4000 c4357 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4342, c4342, 4000, checked4342⟩,
  ⟨4343, c4343, 4000, checked4343⟩,
  ⟨4344, c4344, 4000, checked4344⟩,
  ⟨4345, c4345, 4000, checked4345⟩,
  ⟨4346, c4346, 4000, checked4346⟩,
  ⟨4347, c4347, 4000, checked4347⟩,
  ⟨4348, c4348, 4000, checked4348⟩,
  ⟨4349, c4349, 4000, checked4349⟩,
  ⟨4350, c4350, 4000, checked4350⟩,
  ⟨4351, c4351, 4000, checked4351⟩,
  ⟨4352, c4352, 4000, checked4352⟩,
  ⟨4353, c4353, 4000, checked4353⟩,
  ⟨4354, c4354, 4000, checked4354⟩,
  ⟨4355, c4355, 4000, checked4355⟩,
  ⟨4356, c4356, 4000, checked4356⟩,
  ⟨4357, c4357, 4000, checked4357⟩]

end PA215.ContractShards.Shard033Part7
