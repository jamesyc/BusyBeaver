import PA215.CertifiedContracts
import PA215.Census.C004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard004Part4
open PA215.Contracts PA215.Census

def original582 : RawOriginal := C004.records[70]'(by decide)
theorem original_id582 : original582.index = 582 := by decide

def c582 : Contract := original582.toContract.get (by decide)
theorem binding582 : original582.toContract = some c582 := rfl

theorem checked582 : check 4000 c582 = true := by decide

def original583 : RawOriginal := C004.records[71]'(by decide)
theorem original_id583 : original583.index = 583 := by decide

def c583 : Contract := original583.toContract.get (by decide)
theorem binding583 : original583.toContract = some c583 := rfl

theorem checked583 : check 4000 c583 = true := by decide

def original584 : RawOriginal := C004.records[72]'(by decide)
theorem original_id584 : original584.index = 584 := by decide

def c584 : Contract := original584.toContract.get (by decide)
theorem binding584 : original584.toContract = some c584 := rfl

theorem checked584 : check 4000 c584 = true := by decide

def original585 : RawOriginal := C004.records[73]'(by decide)
theorem original_id585 : original585.index = 585 := by decide

def c585 : Contract := original585.toContract.get (by decide)
theorem binding585 : original585.toContract = some c585 := rfl

theorem checked585 : check 4000 c585 = true := by decide

def original586 : RawOriginal := C004.records[74]'(by decide)
theorem original_id586 : original586.index = 586 := by decide

def c586 : Contract := original586.toContract.get (by decide)
theorem binding586 : original586.toContract = some c586 := rfl

theorem checked586 : check 4000 c586 = true := by decide

def original587 : RawOriginal := C004.records[75]'(by decide)
theorem original_id587 : original587.index = 587 := by decide

def c587 : Contract := original587.toContract.get (by decide)
theorem binding587 : original587.toContract = some c587 := rfl

theorem checked587 : check 4000 c587 = true := by decide

def original588 : RawOriginal := C004.records[76]'(by decide)
theorem original_id588 : original588.index = 588 := by decide

def c588 : Contract := original588.toContract.get (by decide)
theorem binding588 : original588.toContract = some c588 := rfl

theorem checked588 : check 4000 c588 = true := by decide

def original589 : RawOriginal := C004.records[77]'(by decide)
theorem original_id589 : original589.index = 589 := by decide

def c589 : Contract := original589.toContract.get (by decide)
theorem binding589 : original589.toContract = some c589 := rfl

theorem checked589 : check 4000 c589 = true := by decide

def original590 : RawOriginal := C004.records[78]'(by decide)
theorem original_id590 : original590.index = 590 := by decide

def c590 : Contract := original590.toContract.get (by decide)
theorem binding590 : original590.toContract = some c590 := rfl

theorem checked590 : check 4000 c590 = true := by decide

def original591 : RawOriginal := C004.records[79]'(by decide)
theorem original_id591 : original591.index = 591 := by decide

def c591 : Contract := original591.toContract.get (by decide)
theorem binding591 : original591.toContract = some c591 := rfl

theorem checked591 : check 4000 c591 = true := by decide

def original592 : RawOriginal := C004.records[80]'(by decide)
theorem original_id592 : original592.index = 592 := by decide

def c592 : Contract := original592.toContract.get (by decide)
theorem binding592 : original592.toContract = some c592 := rfl

theorem checked592 : check 4000 c592 = true := by decide

def original593 : RawOriginal := C004.records[81]'(by decide)
theorem original_id593 : original593.index = 593 := by decide

def c593 : Contract := original593.toContract.get (by decide)
theorem binding593 : original593.toContract = some c593 := rfl

theorem checked593 : check 4000 c593 = true := by decide

def original594 : RawOriginal := C004.records[82]'(by decide)
theorem original_id594 : original594.index = 594 := by decide

def c594 : Contract := original594.toContract.get (by decide)
theorem binding594 : original594.toContract = some c594 := rfl

theorem checked594 : check 4000 c594 = true := by decide

def original595 : RawOriginal := C004.records[83]'(by decide)
theorem original_id595 : original595.index = 595 := by decide

def c595 : Contract := original595.toContract.get (by decide)
theorem binding595 : original595.toContract = some c595 := rfl

theorem checked595 : check 4000 c595 = true := by decide

def original596 : RawOriginal := C004.records[84]'(by decide)
theorem original_id596 : original596.index = 596 := by decide

def c596 : Contract := original596.toContract.get (by decide)
theorem binding596 : original596.toContract = some c596 := rfl

theorem checked596 : check 4000 c596 = true := by decide

def original597 : RawOriginal := C004.records[85]'(by decide)
theorem original_id597 : original597.index = 597 := by decide

def c597 : Contract := original597.toContract.get (by decide)
theorem binding597 : original597.toContract = some c597 := rfl

theorem checked597 : check 4000 c597 = true := by decide

def records : List Certified := [
  ⟨582, c582, 4000, checked582⟩,
  ⟨583, c583, 4000, checked583⟩,
  ⟨584, c584, 4000, checked584⟩,
  ⟨585, c585, 4000, checked585⟩,
  ⟨586, c586, 4000, checked586⟩,
  ⟨587, c587, 4000, checked587⟩,
  ⟨588, c588, 4000, checked588⟩,
  ⟨589, c589, 4000, checked589⟩,
  ⟨590, c590, 4000, checked590⟩,
  ⟨591, c591, 4000, checked591⟩,
  ⟨592, c592, 4000, checked592⟩,
  ⟨593, c593, 4000, checked593⟩,
  ⟨594, c594, 4000, checked594⟩,
  ⟨595, c595, 4000, checked595⟩,
  ⟨596, c596, 4000, checked596⟩,
  ⟨597, c597, 4000, checked597⟩]

end PA215.ContractShards.Shard004Part4
