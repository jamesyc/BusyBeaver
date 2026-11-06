import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C031
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard031Part1
open PA215.Contracts PA215.Census

def original3990 : RawOriginal := C031.records[22]'(by decide)
theorem original_id3990 : original3990.index = 3990 := by decide

def c3990 : Contract := original3990.toContract.get (by decide)
theorem binding3990 : original3990.toContract = some c3990 := rfl

theorem checked3990 : check 4000 c3990 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3991 : RawOriginal := C031.records[23]'(by decide)
theorem original_id3991 : original3991.index = 3991 := by decide

def c3991 : Contract := original3991.toContract.get (by decide)
theorem binding3991 : original3991.toContract = some c3991 := rfl

theorem checked3991 : check 4000 c3991 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3992 : RawOriginal := C031.records[24]'(by decide)
theorem original_id3992 : original3992.index = 3992 := by decide

def c3992 : Contract := original3992.toContract.get (by decide)
theorem binding3992 : original3992.toContract = some c3992 := rfl

theorem checked3992 : check 4000 c3992 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3993 : RawOriginal := C031.records[25]'(by decide)
theorem original_id3993 : original3993.index = 3993 := by decide

def c3993 : Contract := original3993.toContract.get (by decide)
theorem binding3993 : original3993.toContract = some c3993 := rfl

theorem checked3993 : check 4000 c3993 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3994 : RawOriginal := C031.records[26]'(by decide)
theorem original_id3994 : original3994.index = 3994 := by decide

def c3994 : Contract := original3994.toContract.get (by decide)
theorem binding3994 : original3994.toContract = some c3994 := rfl

theorem checked3994 : check 4000 c3994 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3995 : RawOriginal := C031.records[27]'(by decide)
theorem original_id3995 : original3995.index = 3995 := by decide

def c3995 : Contract := original3995.toContract.get (by decide)
theorem binding3995 : original3995.toContract = some c3995 := rfl

theorem checked3995 : check 4000 c3995 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3996 : RawOriginal := C031.records[28]'(by decide)
theorem original_id3996 : original3996.index = 3996 := by decide

def c3996 : Contract := original3996.toContract.get (by decide)
theorem binding3996 : original3996.toContract = some c3996 := rfl

theorem checked3996 : check 4000 c3996 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3997 : RawOriginal := C031.records[29]'(by decide)
theorem original_id3997 : original3997.index = 3997 := by decide

def c3997 : Contract := original3997.toContract.get (by decide)
theorem binding3997 : original3997.toContract = some c3997 := rfl

theorem checked3997 : check 4000 c3997 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3998 : RawOriginal := C031.records[30]'(by decide)
theorem original_id3998 : original3998.index = 3998 := by decide

def c3998 : Contract := original3998.toContract.get (by decide)
theorem binding3998 : original3998.toContract = some c3998 := rfl

theorem checked3998 : check 4000 c3998 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3999 : RawOriginal := C031.records[31]'(by decide)
theorem original_id3999 : original3999.index = 3999 := by decide

def c3999 : Contract := original3999.toContract.get (by decide)
theorem binding3999 : original3999.toContract = some c3999 := rfl

theorem checked3999 : check 4000 c3999 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4000 : RawOriginal := C031.records[32]'(by decide)
theorem original_id4000 : original4000.index = 4000 := by decide

def c4000 : Contract := original4000.toContract.get (by decide)
theorem binding4000 : original4000.toContract = some c4000 := rfl

theorem checked4000 : check 4000 c4000 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4001 : RawOriginal := C031.records[33]'(by decide)
theorem original_id4001 : original4001.index = 4001 := by decide

def c4001 : Contract := original4001.toContract.get (by decide)
theorem binding4001 : original4001.toContract = some c4001 := rfl

theorem checked4001 : check 4000 c4001 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4002 : RawOriginal := C031.records[34]'(by decide)
theorem original_id4002 : original4002.index = 4002 := by decide

def c4002 : Contract := original4002.toContract.get (by decide)
theorem binding4002 : original4002.toContract = some c4002 := rfl

theorem checked4002 : check 4000 c4002 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4003 : RawOriginal := C031.records[35]'(by decide)
theorem original_id4003 : original4003.index = 4003 := by decide

def c4003 : Contract := original4003.toContract.get (by decide)
theorem binding4003 : original4003.toContract = some c4003 := rfl

theorem checked4003 : check 4000 c4003 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4004 : RawOriginal := C031.records[36]'(by decide)
theorem original_id4004 : original4004.index = 4004 := by decide

def c4004 : Contract := original4004.toContract.get (by decide)
theorem binding4004 : original4004.toContract = some c4004 := rfl

theorem checked4004 : check 4000 c4004 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4005 : RawOriginal := C031.records[37]'(by decide)
theorem original_id4005 : original4005.index = 4005 := by decide

def c4005 : Contract := original4005.toContract.get (by decide)
theorem binding4005 : original4005.toContract = some c4005 := rfl

theorem checked4005 : check 4000 c4005 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3990, c3990, 4000, checked3990⟩,
  ⟨3991, c3991, 4000, checked3991⟩,
  ⟨3992, c3992, 4000, checked3992⟩,
  ⟨3993, c3993, 4000, checked3993⟩,
  ⟨3994, c3994, 4000, checked3994⟩,
  ⟨3995, c3995, 4000, checked3995⟩,
  ⟨3996, c3996, 4000, checked3996⟩,
  ⟨3997, c3997, 4000, checked3997⟩,
  ⟨3998, c3998, 4000, checked3998⟩,
  ⟨3999, c3999, 4000, checked3999⟩,
  ⟨4000, c4000, 4000, checked4000⟩,
  ⟨4001, c4001, 4000, checked4001⟩,
  ⟨4002, c4002, 4000, checked4002⟩,
  ⟨4003, c4003, 4000, checked4003⟩,
  ⟨4004, c4004, 4000, checked4004⟩,
  ⟨4005, c4005, 4000, checked4005⟩]

end PA215.ContractShards.Shard031Part1
