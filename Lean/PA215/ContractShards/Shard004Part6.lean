import PA215.CertifiedContracts
import PA215.Census.C004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard004Part6
open PA215.Contracts PA215.Census

def original614 : RawOriginal := C004.records[102]'(by decide)
theorem original_id614 : original614.index = 614 := by decide

def c614 : Contract := original614.toContract.get (by decide)
theorem binding614 : original614.toContract = some c614 := rfl

theorem checked614 : check 4000 c614 = true := by decide

def original615 : RawOriginal := C004.records[103]'(by decide)
theorem original_id615 : original615.index = 615 := by decide

def c615 : Contract := original615.toContract.get (by decide)
theorem binding615 : original615.toContract = some c615 := rfl

theorem checked615 : check 4000 c615 = true := by decide

def original616 : RawOriginal := C004.records[104]'(by decide)
theorem original_id616 : original616.index = 616 := by decide

def c616 : Contract := original616.toContract.get (by decide)
theorem binding616 : original616.toContract = some c616 := rfl

theorem checked616 : check 4000 c616 = true := by decide

def original617 : RawOriginal := C004.records[105]'(by decide)
theorem original_id617 : original617.index = 617 := by decide

def c617 : Contract := original617.toContract.get (by decide)
theorem binding617 : original617.toContract = some c617 := rfl

theorem checked617 : check 4000 c617 = true := by decide

def original618 : RawOriginal := C004.records[106]'(by decide)
theorem original_id618 : original618.index = 618 := by decide

def c618 : Contract := original618.toContract.get (by decide)
theorem binding618 : original618.toContract = some c618 := rfl

theorem checked618 : check 4000 c618 = true := by decide

def original619 : RawOriginal := C004.records[107]'(by decide)
theorem original_id619 : original619.index = 619 := by decide

def c619 : Contract := original619.toContract.get (by decide)
theorem binding619 : original619.toContract = some c619 := rfl

theorem checked619 : check 4000 c619 = true := by decide

def original620 : RawOriginal := C004.records[108]'(by decide)
theorem original_id620 : original620.index = 620 := by decide

def c620 : Contract := original620.toContract.get (by decide)
theorem binding620 : original620.toContract = some c620 := rfl

theorem checked620 : check 4000 c620 = true := by decide

def original621 : RawOriginal := C004.records[109]'(by decide)
theorem original_id621 : original621.index = 621 := by decide

def c621 : Contract := original621.toContract.get (by decide)
theorem binding621 : original621.toContract = some c621 := rfl

theorem checked621 : check 4000 c621 = true := by decide

def original622 : RawOriginal := C004.records[110]'(by decide)
theorem original_id622 : original622.index = 622 := by decide

def c622 : Contract := original622.toContract.get (by decide)
theorem binding622 : original622.toContract = some c622 := rfl

theorem checked622 : check 4000 c622 = true := by decide

def original623 : RawOriginal := C004.records[111]'(by decide)
theorem original_id623 : original623.index = 623 := by decide

def c623 : Contract := original623.toContract.get (by decide)
theorem binding623 : original623.toContract = some c623 := rfl

theorem checked623 : check 4000 c623 = true := by decide

def original624 : RawOriginal := C004.records[112]'(by decide)
theorem original_id624 : original624.index = 624 := by decide

def c624 : Contract := original624.toContract.get (by decide)
theorem binding624 : original624.toContract = some c624 := rfl

theorem checked624 : check 4000 c624 = true := by decide

def original625 : RawOriginal := C004.records[113]'(by decide)
theorem original_id625 : original625.index = 625 := by decide

def c625 : Contract := original625.toContract.get (by decide)
theorem binding625 : original625.toContract = some c625 := rfl

theorem checked625 : check 4000 c625 = true := by decide

def original626 : RawOriginal := C004.records[114]'(by decide)
theorem original_id626 : original626.index = 626 := by decide

def c626 : Contract := original626.toContract.get (by decide)
theorem binding626 : original626.toContract = some c626 := rfl

theorem checked626 : check 4000 c626 = true := by decide

def original627 : RawOriginal := C004.records[115]'(by decide)
theorem original_id627 : original627.index = 627 := by decide

def c627 : Contract := original627.toContract.get (by decide)
theorem binding627 : original627.toContract = some c627 := rfl

theorem checked627 : check 4000 c627 = true := by decide

def original628 : RawOriginal := C004.records[116]'(by decide)
theorem original_id628 : original628.index = 628 := by decide

def c628 : Contract := original628.toContract.get (by decide)
theorem binding628 : original628.toContract = some c628 := rfl

theorem checked628 : check 4000 c628 = true := by decide

def original629 : RawOriginal := C004.records[117]'(by decide)
theorem original_id629 : original629.index = 629 := by decide

def c629 : Contract := original629.toContract.get (by decide)
theorem binding629 : original629.toContract = some c629 := rfl

theorem checked629 : check 4000 c629 = true := by decide

def records : List Certified := [
  ⟨614, c614, 4000, checked614⟩,
  ⟨615, c615, 4000, checked615⟩,
  ⟨616, c616, 4000, checked616⟩,
  ⟨617, c617, 4000, checked617⟩,
  ⟨618, c618, 4000, checked618⟩,
  ⟨619, c619, 4000, checked619⟩,
  ⟨620, c620, 4000, checked620⟩,
  ⟨621, c621, 4000, checked621⟩,
  ⟨622, c622, 4000, checked622⟩,
  ⟨623, c623, 4000, checked623⟩,
  ⟨624, c624, 4000, checked624⟩,
  ⟨625, c625, 4000, checked625⟩,
  ⟨626, c626, 4000, checked626⟩,
  ⟨627, c627, 4000, checked627⟩,
  ⟨628, c628, 4000, checked628⟩,
  ⟨629, c629, 4000, checked629⟩]

end PA215.ContractShards.Shard004Part6
