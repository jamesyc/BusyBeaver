import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C035
import PA215.Census.C036
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard035Part7
open PA215.Contracts PA215.Census

def original4598 : RawOriginal := C035.records[118]'(by decide)
theorem original_id4598 : original4598.index = 4598 := by decide

def c4598 : Contract := original4598.toContract.get (by decide)
theorem binding4598 : original4598.toContract = some c4598 := rfl

theorem checked4598 : check 4000 c4598 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4599 : RawOriginal := C035.records[119]'(by decide)
theorem original_id4599 : original4599.index = 4599 := by decide

def c4599 : Contract := original4599.toContract.get (by decide)
theorem binding4599 : original4599.toContract = some c4599 := rfl

theorem checked4599 : check 4000 c4599 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4600 : RawOriginal := C035.records[120]'(by decide)
theorem original_id4600 : original4600.index = 4600 := by decide

def c4600 : Contract := original4600.toContract.get (by decide)
theorem binding4600 : original4600.toContract = some c4600 := rfl

theorem checked4600 : check 4000 c4600 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4601 : RawOriginal := C035.records[121]'(by decide)
theorem original_id4601 : original4601.index = 4601 := by decide

def c4601 : Contract := original4601.toContract.get (by decide)
theorem binding4601 : original4601.toContract = some c4601 := rfl

theorem checked4601 : check 4000 c4601 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4602 : RawOriginal := C035.records[122]'(by decide)
theorem original_id4602 : original4602.index = 4602 := by decide

def c4602 : Contract := original4602.toContract.get (by decide)
theorem binding4602 : original4602.toContract = some c4602 := rfl

theorem checked4602 : check 4000 c4602 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4603 : RawOriginal := C035.records[123]'(by decide)
theorem original_id4603 : original4603.index = 4603 := by decide

def c4603 : Contract := original4603.toContract.get (by decide)
theorem binding4603 : original4603.toContract = some c4603 := rfl

theorem checked4603 : check 4000 c4603 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4604 : RawOriginal := C035.records[124]'(by decide)
theorem original_id4604 : original4604.index = 4604 := by decide

def c4604 : Contract := original4604.toContract.get (by decide)
theorem binding4604 : original4604.toContract = some c4604 := rfl

theorem checked4604 : check 4000 c4604 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4605 : RawOriginal := C035.records[125]'(by decide)
theorem original_id4605 : original4605.index = 4605 := by decide

def c4605 : Contract := original4605.toContract.get (by decide)
theorem binding4605 : original4605.toContract = some c4605 := rfl

theorem checked4605 : check 4000 c4605 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4606 : RawOriginal := C035.records[126]'(by decide)
theorem original_id4606 : original4606.index = 4606 := by decide

def c4606 : Contract := original4606.toContract.get (by decide)
theorem binding4606 : original4606.toContract = some c4606 := rfl

theorem checked4606 : check 4000 c4606 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4607 : RawOriginal := C035.records[127]'(by decide)
theorem original_id4607 : original4607.index = 4607 := by decide

def c4607 : Contract := original4607.toContract.get (by decide)
theorem binding4607 : original4607.toContract = some c4607 := rfl

theorem checked4607 : check 4000 c4607 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4608 : RawOriginal := C036.records[0]'(by decide)
theorem original_id4608 : original4608.index = 4608 := by decide

def c4608 : Contract := original4608.toContract.get (by decide)
theorem binding4608 : original4608.toContract = some c4608 := rfl

theorem checked4608 : check 4000 c4608 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4609 : RawOriginal := C036.records[1]'(by decide)
theorem original_id4609 : original4609.index = 4609 := by decide

def c4609 : Contract := original4609.toContract.get (by decide)
theorem binding4609 : original4609.toContract = some c4609 := rfl

theorem checked4609 : check 4000 c4609 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4610 : RawOriginal := C036.records[2]'(by decide)
theorem original_id4610 : original4610.index = 4610 := by decide

def c4610 : Contract := original4610.toContract.get (by decide)
theorem binding4610 : original4610.toContract = some c4610 := rfl

theorem checked4610 : check 4000 c4610 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4611 : RawOriginal := C036.records[3]'(by decide)
theorem original_id4611 : original4611.index = 4611 := by decide

def c4611 : Contract := original4611.toContract.get (by decide)
theorem binding4611 : original4611.toContract = some c4611 := rfl

theorem checked4611 : check 4000 c4611 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4612 : RawOriginal := C036.records[4]'(by decide)
theorem original_id4612 : original4612.index = 4612 := by decide

def c4612 : Contract := original4612.toContract.get (by decide)
theorem binding4612 : original4612.toContract = some c4612 := rfl

theorem checked4612 : check 4000 c4612 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4613 : RawOriginal := C036.records[5]'(by decide)
theorem original_id4613 : original4613.index = 4613 := by decide

def c4613 : Contract := original4613.toContract.get (by decide)
theorem binding4613 : original4613.toContract = some c4613 := rfl

theorem checked4613 : check 4000 c4613 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4598, c4598, 4000, checked4598⟩,
  ⟨4599, c4599, 4000, checked4599⟩,
  ⟨4600, c4600, 4000, checked4600⟩,
  ⟨4601, c4601, 4000, checked4601⟩,
  ⟨4602, c4602, 4000, checked4602⟩,
  ⟨4603, c4603, 4000, checked4603⟩,
  ⟨4604, c4604, 4000, checked4604⟩,
  ⟨4605, c4605, 4000, checked4605⟩,
  ⟨4606, c4606, 4000, checked4606⟩,
  ⟨4607, c4607, 4000, checked4607⟩,
  ⟨4608, c4608, 4000, checked4608⟩,
  ⟨4609, c4609, 4000, checked4609⟩,
  ⟨4610, c4610, 4000, checked4610⟩,
  ⟨4611, c4611, 4000, checked4611⟩,
  ⟨4612, c4612, 4000, checked4612⟩,
  ⟨4613, c4613, 4000, checked4613⟩]

end PA215.ContractShards.Shard035Part7
