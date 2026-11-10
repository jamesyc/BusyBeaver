import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C040
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard040Part0
open PA215.Contracts PA215.Census

def original5133 : RawOriginal := C040.records[13]'(by decide)
theorem original_id5133 : original5133.index = 5133 := by decide

def c5133 : Contract := original5133.toContract.get (by decide)
theorem binding5133 : original5133.toContract = some c5133 := rfl

theorem checked5133 : check 4000 c5133 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨5133, c5133, 4000, checked5133⟩]

end PA215.ContractShards.Shard040Part0
