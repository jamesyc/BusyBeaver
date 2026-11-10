import PA215.CertifiedContracts
import PA215.Census.C003
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard003Part6
open PA215.Contracts PA215.Census

def original486 : RawOriginal := C003.records[102]'(by decide)
theorem original_id486 : original486.index = 486 := by decide

def c486 : Contract := original486.toContract.get (by decide)
theorem binding486 : original486.toContract = some c486 := rfl

theorem checked486 : check 4000 c486 = true := by decide

def original487 : RawOriginal := C003.records[103]'(by decide)
theorem original_id487 : original487.index = 487 := by decide

def c487 : Contract := original487.toContract.get (by decide)
theorem binding487 : original487.toContract = some c487 := rfl

theorem checked487 : check 4000 c487 = true := by decide

def original488 : RawOriginal := C003.records[104]'(by decide)
theorem original_id488 : original488.index = 488 := by decide

def c488 : Contract := original488.toContract.get (by decide)
theorem binding488 : original488.toContract = some c488 := rfl

theorem checked488 : check 4000 c488 = true := by decide

def original489 : RawOriginal := C003.records[105]'(by decide)
theorem original_id489 : original489.index = 489 := by decide

def c489 : Contract := original489.toContract.get (by decide)
theorem binding489 : original489.toContract = some c489 := rfl

theorem checked489 : check 4000 c489 = true := by decide

def original490 : RawOriginal := C003.records[106]'(by decide)
theorem original_id490 : original490.index = 490 := by decide

def c490 : Contract := original490.toContract.get (by decide)
theorem binding490 : original490.toContract = some c490 := rfl

theorem checked490 : check 4000 c490 = true := by decide

def original491 : RawOriginal := C003.records[107]'(by decide)
theorem original_id491 : original491.index = 491 := by decide

def c491 : Contract := original491.toContract.get (by decide)
theorem binding491 : original491.toContract = some c491 := rfl

theorem checked491 : check 4000 c491 = true := by decide

def original492 : RawOriginal := C003.records[108]'(by decide)
theorem original_id492 : original492.index = 492 := by decide

def c492 : Contract := original492.toContract.get (by decide)
theorem binding492 : original492.toContract = some c492 := rfl

theorem checked492 : check 4000 c492 = true := by decide

def original493 : RawOriginal := C003.records[109]'(by decide)
theorem original_id493 : original493.index = 493 := by decide

def c493 : Contract := original493.toContract.get (by decide)
theorem binding493 : original493.toContract = some c493 := rfl

theorem checked493 : check 4000 c493 = true := by decide

def original494 : RawOriginal := C003.records[110]'(by decide)
theorem original_id494 : original494.index = 494 := by decide

def c494 : Contract := original494.toContract.get (by decide)
theorem binding494 : original494.toContract = some c494 := rfl

theorem checked494 : check 4000 c494 = true := by decide

def original495 : RawOriginal := C003.records[111]'(by decide)
theorem original_id495 : original495.index = 495 := by decide

def c495 : Contract := original495.toContract.get (by decide)
theorem binding495 : original495.toContract = some c495 := rfl

theorem checked495 : check 4000 c495 = true := by decide

def original496 : RawOriginal := C003.records[112]'(by decide)
theorem original_id496 : original496.index = 496 := by decide

def c496 : Contract := original496.toContract.get (by decide)
theorem binding496 : original496.toContract = some c496 := rfl

theorem checked496 : check 4000 c496 = true := by decide

def original497 : RawOriginal := C003.records[113]'(by decide)
theorem original_id497 : original497.index = 497 := by decide

def c497 : Contract := original497.toContract.get (by decide)
theorem binding497 : original497.toContract = some c497 := rfl

theorem checked497 : check 4000 c497 = true := by decide

def original498 : RawOriginal := C003.records[114]'(by decide)
theorem original_id498 : original498.index = 498 := by decide

def c498 : Contract := original498.toContract.get (by decide)
theorem binding498 : original498.toContract = some c498 := rfl

theorem checked498 : check 4000 c498 = true := by decide

def original499 : RawOriginal := C003.records[115]'(by decide)
theorem original_id499 : original499.index = 499 := by decide

def c499 : Contract := original499.toContract.get (by decide)
theorem binding499 : original499.toContract = some c499 := rfl

theorem checked499 : check 4000 c499 = true := by decide

def original500 : RawOriginal := C003.records[116]'(by decide)
theorem original_id500 : original500.index = 500 := by decide

def c500 : Contract := original500.toContract.get (by decide)
theorem binding500 : original500.toContract = some c500 := rfl

theorem checked500 : check 4000 c500 = true := by decide

def original501 : RawOriginal := C003.records[117]'(by decide)
theorem original_id501 : original501.index = 501 := by decide

def c501 : Contract := original501.toContract.get (by decide)
theorem binding501 : original501.toContract = some c501 := rfl

theorem checked501 : check 4000 c501 = true := by decide

def records : List Certified := [
  ⟨486, c486, 4000, checked486⟩,
  ⟨487, c487, 4000, checked487⟩,
  ⟨488, c488, 4000, checked488⟩,
  ⟨489, c489, 4000, checked489⟩,
  ⟨490, c490, 4000, checked490⟩,
  ⟨491, c491, 4000, checked491⟩,
  ⟨492, c492, 4000, checked492⟩,
  ⟨493, c493, 4000, checked493⟩,
  ⟨494, c494, 4000, checked494⟩,
  ⟨495, c495, 4000, checked495⟩,
  ⟨496, c496, 4000, checked496⟩,
  ⟨497, c497, 4000, checked497⟩,
  ⟨498, c498, 4000, checked498⟩,
  ⟨499, c499, 4000, checked499⟩,
  ⟨500, c500, 4000, checked500⟩,
  ⟨501, c501, 4000, checked501⟩]

end PA215.ContractShards.Shard003Part6
