import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C038
import PA215.Census.C039
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard038Part7
open PA215.Contracts PA215.Census

def original4983 : RawOriginal := C038.records[119]'(by decide)
theorem original_id4983 : original4983.index = 4983 := by decide

def c4983 : Contract := original4983.toContract.get (by decide)
theorem binding4983 : original4983.toContract = some c4983 := rfl

theorem checked4983 : check 4000 c4983 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4984 : RawOriginal := C038.records[120]'(by decide)
theorem original_id4984 : original4984.index = 4984 := by decide

def c4984 : Contract := original4984.toContract.get (by decide)
theorem binding4984 : original4984.toContract = some c4984 := rfl

theorem checked4984 : check 4000 c4984 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4985 : RawOriginal := C038.records[121]'(by decide)
theorem original_id4985 : original4985.index = 4985 := by decide

def c4985 : Contract := original4985.toContract.get (by decide)
theorem binding4985 : original4985.toContract = some c4985 := rfl

theorem checked4985 : check 4000 c4985 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4986 : RawOriginal := C038.records[122]'(by decide)
theorem original_id4986 : original4986.index = 4986 := by decide

def c4986 : Contract := original4986.toContract.get (by decide)
theorem binding4986 : original4986.toContract = some c4986 := rfl

theorem checked4986 : check 4000 c4986 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4987 : RawOriginal := C038.records[123]'(by decide)
theorem original_id4987 : original4987.index = 4987 := by decide

def c4987 : Contract := original4987.toContract.get (by decide)
theorem binding4987 : original4987.toContract = some c4987 := rfl

theorem checked4987 : check 4000 c4987 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4988 : RawOriginal := C038.records[124]'(by decide)
theorem original_id4988 : original4988.index = 4988 := by decide

def c4988 : Contract := original4988.toContract.get (by decide)
theorem binding4988 : original4988.toContract = some c4988 := rfl

theorem checked4988 : check 4000 c4988 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4989 : RawOriginal := C038.records[125]'(by decide)
theorem original_id4989 : original4989.index = 4989 := by decide

def c4989 : Contract := original4989.toContract.get (by decide)
theorem binding4989 : original4989.toContract = some c4989 := rfl

theorem checked4989 : check 4000 c4989 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4990 : RawOriginal := C038.records[126]'(by decide)
theorem original_id4990 : original4990.index = 4990 := by decide

def c4990 : Contract := original4990.toContract.get (by decide)
theorem binding4990 : original4990.toContract = some c4990 := rfl

theorem checked4990 : check 4000 c4990 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4991 : RawOriginal := C038.records[127]'(by decide)
theorem original_id4991 : original4991.index = 4991 := by decide

def c4991 : Contract := original4991.toContract.get (by decide)
theorem binding4991 : original4991.toContract = some c4991 := rfl

theorem checked4991 : check 4000 c4991 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4992 : RawOriginal := C039.records[0]'(by decide)
theorem original_id4992 : original4992.index = 4992 := by decide

def c4992 : Contract := original4992.toContract.get (by decide)
theorem binding4992 : original4992.toContract = some c4992 := rfl

theorem checked4992 : check 4000 c4992 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4993 : RawOriginal := C039.records[1]'(by decide)
theorem original_id4993 : original4993.index = 4993 := by decide

def c4993 : Contract := original4993.toContract.get (by decide)
theorem binding4993 : original4993.toContract = some c4993 := rfl

theorem checked4993 : check 4000 c4993 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4994 : RawOriginal := C039.records[2]'(by decide)
theorem original_id4994 : original4994.index = 4994 := by decide

def c4994 : Contract := original4994.toContract.get (by decide)
theorem binding4994 : original4994.toContract = some c4994 := rfl

theorem checked4994 : check 4000 c4994 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4995 : RawOriginal := C039.records[3]'(by decide)
theorem original_id4995 : original4995.index = 4995 := by decide

def c4995 : Contract := original4995.toContract.get (by decide)
theorem binding4995 : original4995.toContract = some c4995 := rfl

theorem checked4995 : check 4000 c4995 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4996 : RawOriginal := C039.records[4]'(by decide)
theorem original_id4996 : original4996.index = 4996 := by decide

def c4996 : Contract := original4996.toContract.get (by decide)
theorem binding4996 : original4996.toContract = some c4996 := rfl

theorem checked4996 : check 4000 c4996 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4997 : RawOriginal := C039.records[5]'(by decide)
theorem original_id4997 : original4997.index = 4997 := by decide

def c4997 : Contract := original4997.toContract.get (by decide)
theorem binding4997 : original4997.toContract = some c4997 := rfl

theorem checked4997 : check 4000 c4997 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4998 : RawOriginal := C039.records[6]'(by decide)
theorem original_id4998 : original4998.index = 4998 := by decide

def c4998 : Contract := original4998.toContract.get (by decide)
theorem binding4998 : original4998.toContract = some c4998 := rfl

theorem checked4998 : check 4000 c4998 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4983, c4983, 4000, checked4983⟩,
  ⟨4984, c4984, 4000, checked4984⟩,
  ⟨4985, c4985, 4000, checked4985⟩,
  ⟨4986, c4986, 4000, checked4986⟩,
  ⟨4987, c4987, 4000, checked4987⟩,
  ⟨4988, c4988, 4000, checked4988⟩,
  ⟨4989, c4989, 4000, checked4989⟩,
  ⟨4990, c4990, 4000, checked4990⟩,
  ⟨4991, c4991, 4000, checked4991⟩,
  ⟨4992, c4992, 4000, checked4992⟩,
  ⟨4993, c4993, 4000, checked4993⟩,
  ⟨4994, c4994, 4000, checked4994⟩,
  ⟨4995, c4995, 4000, checked4995⟩,
  ⟨4996, c4996, 4000, checked4996⟩,
  ⟨4997, c4997, 4000, checked4997⟩,
  ⟨4998, c4998, 4000, checked4998⟩]

end PA215.ContractShards.Shard038Part7
