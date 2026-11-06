import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C034
import PA215.Census.C035
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard034Part7
open PA215.Contracts PA215.Census

def original4470 : RawOriginal := C034.records[118]'(by decide)
theorem original_id4470 : original4470.index = 4470 := by decide

def c4470 : Contract := original4470.toContract.get (by decide)
theorem binding4470 : original4470.toContract = some c4470 := rfl

theorem checked4470 : check 4000 c4470 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4471 : RawOriginal := C034.records[119]'(by decide)
theorem original_id4471 : original4471.index = 4471 := by decide

def c4471 : Contract := original4471.toContract.get (by decide)
theorem binding4471 : original4471.toContract = some c4471 := rfl

theorem checked4471 : check 4000 c4471 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4472 : RawOriginal := C034.records[120]'(by decide)
theorem original_id4472 : original4472.index = 4472 := by decide

def c4472 : Contract := original4472.toContract.get (by decide)
theorem binding4472 : original4472.toContract = some c4472 := rfl

theorem checked4472 : check 4000 c4472 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4473 : RawOriginal := C034.records[121]'(by decide)
theorem original_id4473 : original4473.index = 4473 := by decide

def c4473 : Contract := original4473.toContract.get (by decide)
theorem binding4473 : original4473.toContract = some c4473 := rfl

theorem checked4473 : check 4000 c4473 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4474 : RawOriginal := C034.records[122]'(by decide)
theorem original_id4474 : original4474.index = 4474 := by decide

def c4474 : Contract := original4474.toContract.get (by decide)
theorem binding4474 : original4474.toContract = some c4474 := rfl

theorem checked4474 : check 4000 c4474 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4475 : RawOriginal := C034.records[123]'(by decide)
theorem original_id4475 : original4475.index = 4475 := by decide

def c4475 : Contract := original4475.toContract.get (by decide)
theorem binding4475 : original4475.toContract = some c4475 := rfl

theorem checked4475 : check 4000 c4475 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4476 : RawOriginal := C034.records[124]'(by decide)
theorem original_id4476 : original4476.index = 4476 := by decide

def c4476 : Contract := original4476.toContract.get (by decide)
theorem binding4476 : original4476.toContract = some c4476 := rfl

theorem checked4476 : check 4000 c4476 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4477 : RawOriginal := C034.records[125]'(by decide)
theorem original_id4477 : original4477.index = 4477 := by decide

def c4477 : Contract := original4477.toContract.get (by decide)
theorem binding4477 : original4477.toContract = some c4477 := rfl

theorem checked4477 : check 4000 c4477 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4478 : RawOriginal := C034.records[126]'(by decide)
theorem original_id4478 : original4478.index = 4478 := by decide

def c4478 : Contract := original4478.toContract.get (by decide)
theorem binding4478 : original4478.toContract = some c4478 := rfl

theorem checked4478 : check 4000 c4478 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4479 : RawOriginal := C034.records[127]'(by decide)
theorem original_id4479 : original4479.index = 4479 := by decide

def c4479 : Contract := original4479.toContract.get (by decide)
theorem binding4479 : original4479.toContract = some c4479 := rfl

theorem checked4479 : check 4000 c4479 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4480 : RawOriginal := C035.records[0]'(by decide)
theorem original_id4480 : original4480.index = 4480 := by decide

def c4480 : Contract := original4480.toContract.get (by decide)
theorem binding4480 : original4480.toContract = some c4480 := rfl

theorem checked4480 : check 4000 c4480 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4481 : RawOriginal := C035.records[1]'(by decide)
theorem original_id4481 : original4481.index = 4481 := by decide

def c4481 : Contract := original4481.toContract.get (by decide)
theorem binding4481 : original4481.toContract = some c4481 := rfl

theorem checked4481 : check 4000 c4481 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4482 : RawOriginal := C035.records[2]'(by decide)
theorem original_id4482 : original4482.index = 4482 := by decide

def c4482 : Contract := original4482.toContract.get (by decide)
theorem binding4482 : original4482.toContract = some c4482 := rfl

theorem checked4482 : check 4000 c4482 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4483 : RawOriginal := C035.records[3]'(by decide)
theorem original_id4483 : original4483.index = 4483 := by decide

def c4483 : Contract := original4483.toContract.get (by decide)
theorem binding4483 : original4483.toContract = some c4483 := rfl

theorem checked4483 : check 4000 c4483 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4484 : RawOriginal := C035.records[4]'(by decide)
theorem original_id4484 : original4484.index = 4484 := by decide

def c4484 : Contract := original4484.toContract.get (by decide)
theorem binding4484 : original4484.toContract = some c4484 := rfl

theorem checked4484 : check 4000 c4484 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4485 : RawOriginal := C035.records[5]'(by decide)
theorem original_id4485 : original4485.index = 4485 := by decide

def c4485 : Contract := original4485.toContract.get (by decide)
theorem binding4485 : original4485.toContract = some c4485 := rfl

theorem checked4485 : check 4000 c4485 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4470, c4470, 4000, checked4470⟩,
  ⟨4471, c4471, 4000, checked4471⟩,
  ⟨4472, c4472, 4000, checked4472⟩,
  ⟨4473, c4473, 4000, checked4473⟩,
  ⟨4474, c4474, 4000, checked4474⟩,
  ⟨4475, c4475, 4000, checked4475⟩,
  ⟨4476, c4476, 4000, checked4476⟩,
  ⟨4477, c4477, 4000, checked4477⟩,
  ⟨4478, c4478, 4000, checked4478⟩,
  ⟨4479, c4479, 4000, checked4479⟩,
  ⟨4480, c4480, 4000, checked4480⟩,
  ⟨4481, c4481, 4000, checked4481⟩,
  ⟨4482, c4482, 4000, checked4482⟩,
  ⟨4483, c4483, 4000, checked4483⟩,
  ⟨4484, c4484, 4000, checked4484⟩,
  ⟨4485, c4485, 4000, checked4485⟩]

end PA215.ContractShards.Shard034Part7
