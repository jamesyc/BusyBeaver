import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C039
import PA215.Census.C040
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard039Part7
open PA215.Contracts PA215.Census

def original5117 : RawOriginal := C039.records[125]'(by decide)
theorem original_id5117 : original5117.index = 5117 := by decide

def c5117 : Contract := original5117.toContract.get (by decide)
theorem binding5117 : original5117.toContract = some c5117 := rfl

theorem checked5117 : check 4000 c5117 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5118 : RawOriginal := C039.records[126]'(by decide)
theorem original_id5118 : original5118.index = 5118 := by decide

def c5118 : Contract := original5118.toContract.get (by decide)
theorem binding5118 : original5118.toContract = some c5118 := rfl

theorem checked5118 : check 4000 c5118 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5119 : RawOriginal := C039.records[127]'(by decide)
theorem original_id5119 : original5119.index = 5119 := by decide

def c5119 : Contract := original5119.toContract.get (by decide)
theorem binding5119 : original5119.toContract = some c5119 := rfl

theorem checked5119 : check 4000 c5119 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5120 : RawOriginal := C040.records[0]'(by decide)
theorem original_id5120 : original5120.index = 5120 := by decide

def c5120 : Contract := original5120.toContract.get (by decide)
theorem binding5120 : original5120.toContract = some c5120 := rfl

theorem checked5120 : check 4000 c5120 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5121 : RawOriginal := C040.records[1]'(by decide)
theorem original_id5121 : original5121.index = 5121 := by decide

def c5121 : Contract := original5121.toContract.get (by decide)
theorem binding5121 : original5121.toContract = some c5121 := rfl

theorem checked5121 : check 4000 c5121 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5122 : RawOriginal := C040.records[2]'(by decide)
theorem original_id5122 : original5122.index = 5122 := by decide

def c5122 : Contract := original5122.toContract.get (by decide)
theorem binding5122 : original5122.toContract = some c5122 := rfl

theorem checked5122 : check 4000 c5122 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5123 : RawOriginal := C040.records[3]'(by decide)
theorem original_id5123 : original5123.index = 5123 := by decide

def c5123 : Contract := original5123.toContract.get (by decide)
theorem binding5123 : original5123.toContract = some c5123 := rfl

theorem checked5123 : check 4000 c5123 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5124 : RawOriginal := C040.records[4]'(by decide)
theorem original_id5124 : original5124.index = 5124 := by decide

def c5124 : Contract := original5124.toContract.get (by decide)
theorem binding5124 : original5124.toContract = some c5124 := rfl

theorem checked5124 : check 4000 c5124 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5125 : RawOriginal := C040.records[5]'(by decide)
theorem original_id5125 : original5125.index = 5125 := by decide

def c5125 : Contract := original5125.toContract.get (by decide)
theorem binding5125 : original5125.toContract = some c5125 := rfl

theorem checked5125 : check 4000 c5125 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5126 : RawOriginal := C040.records[6]'(by decide)
theorem original_id5126 : original5126.index = 5126 := by decide

def c5126 : Contract := original5126.toContract.get (by decide)
theorem binding5126 : original5126.toContract = some c5126 := rfl

theorem checked5126 : check 4000 c5126 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5127 : RawOriginal := C040.records[7]'(by decide)
theorem original_id5127 : original5127.index = 5127 := by decide

def c5127 : Contract := original5127.toContract.get (by decide)
theorem binding5127 : original5127.toContract = some c5127 := rfl

theorem checked5127 : check 4000 c5127 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5128 : RawOriginal := C040.records[8]'(by decide)
theorem original_id5128 : original5128.index = 5128 := by decide

def c5128 : Contract := original5128.toContract.get (by decide)
theorem binding5128 : original5128.toContract = some c5128 := rfl

theorem checked5128 : check 4000 c5128 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5129 : RawOriginal := C040.records[9]'(by decide)
theorem original_id5129 : original5129.index = 5129 := by decide

def c5129 : Contract := original5129.toContract.get (by decide)
theorem binding5129 : original5129.toContract = some c5129 := rfl

theorem checked5129 : check 4000 c5129 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5130 : RawOriginal := C040.records[10]'(by decide)
theorem original_id5130 : original5130.index = 5130 := by decide

def c5130 : Contract := original5130.toContract.get (by decide)
theorem binding5130 : original5130.toContract = some c5130 := rfl

theorem checked5130 : check 4000 c5130 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5131 : RawOriginal := C040.records[11]'(by decide)
theorem original_id5131 : original5131.index = 5131 := by decide

def c5131 : Contract := original5131.toContract.get (by decide)
theorem binding5131 : original5131.toContract = some c5131 := rfl

theorem checked5131 : check 4000 c5131 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5132 : RawOriginal := C040.records[12]'(by decide)
theorem original_id5132 : original5132.index = 5132 := by decide

def c5132 : Contract := original5132.toContract.get (by decide)
theorem binding5132 : original5132.toContract = some c5132 := rfl

theorem checked5132 : check 4000 c5132 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨5117, c5117, 4000, checked5117⟩,
  ⟨5118, c5118, 4000, checked5118⟩,
  ⟨5119, c5119, 4000, checked5119⟩,
  ⟨5120, c5120, 4000, checked5120⟩,
  ⟨5121, c5121, 4000, checked5121⟩,
  ⟨5122, c5122, 4000, checked5122⟩,
  ⟨5123, c5123, 4000, checked5123⟩,
  ⟨5124, c5124, 4000, checked5124⟩,
  ⟨5125, c5125, 4000, checked5125⟩,
  ⟨5126, c5126, 4000, checked5126⟩,
  ⟨5127, c5127, 4000, checked5127⟩,
  ⟨5128, c5128, 4000, checked5128⟩,
  ⟨5129, c5129, 4000, checked5129⟩,
  ⟨5130, c5130, 4000, checked5130⟩,
  ⟨5131, c5131, 4000, checked5131⟩,
  ⟨5132, c5132, 4000, checked5132⟩]

end PA215.ContractShards.Shard039Part7
