import PA215.CertifiedContracts
import PA215.Census.C005
import PA215.Census.C006
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard005Part7
open PA215.Contracts PA215.Census

def original758 : RawOriginal := C005.records[118]'(by decide)
theorem original_id758 : original758.index = 758 := by decide

def c758 : Contract := original758.toContract.get (by decide)
theorem binding758 : original758.toContract = some c758 := rfl

theorem checked758 : check 4000 c758 = true := by decide

def original759 : RawOriginal := C005.records[119]'(by decide)
theorem original_id759 : original759.index = 759 := by decide

def c759 : Contract := original759.toContract.get (by decide)
theorem binding759 : original759.toContract = some c759 := rfl

theorem checked759 : check 4000 c759 = true := by decide

def original760 : RawOriginal := C005.records[120]'(by decide)
theorem original_id760 : original760.index = 760 := by decide

def c760 : Contract := original760.toContract.get (by decide)
theorem binding760 : original760.toContract = some c760 := rfl

theorem checked760 : check 4000 c760 = true := by decide

def original761 : RawOriginal := C005.records[121]'(by decide)
theorem original_id761 : original761.index = 761 := by decide

def c761 : Contract := original761.toContract.get (by decide)
theorem binding761 : original761.toContract = some c761 := rfl

theorem checked761 : check 4000 c761 = true := by decide

def original762 : RawOriginal := C005.records[122]'(by decide)
theorem original_id762 : original762.index = 762 := by decide

def c762 : Contract := original762.toContract.get (by decide)
theorem binding762 : original762.toContract = some c762 := rfl

theorem checked762 : check 4000 c762 = true := by decide

def original763 : RawOriginal := C005.records[123]'(by decide)
theorem original_id763 : original763.index = 763 := by decide

def c763 : Contract := original763.toContract.get (by decide)
theorem binding763 : original763.toContract = some c763 := rfl

theorem checked763 : check 4000 c763 = true := by decide

def original764 : RawOriginal := C005.records[124]'(by decide)
theorem original_id764 : original764.index = 764 := by decide

def c764 : Contract := original764.toContract.get (by decide)
theorem binding764 : original764.toContract = some c764 := rfl

theorem checked764 : check 4000 c764 = true := by decide

def original765 : RawOriginal := C005.records[125]'(by decide)
theorem original_id765 : original765.index = 765 := by decide

def c765 : Contract := original765.toContract.get (by decide)
theorem binding765 : original765.toContract = some c765 := rfl

theorem checked765 : check 4000 c765 = true := by decide

def original766 : RawOriginal := C005.records[126]'(by decide)
theorem original_id766 : original766.index = 766 := by decide

def c766 : Contract := original766.toContract.get (by decide)
theorem binding766 : original766.toContract = some c766 := rfl

theorem checked766 : check 4000 c766 = true := by decide

def original767 : RawOriginal := C005.records[127]'(by decide)
theorem original_id767 : original767.index = 767 := by decide

def c767 : Contract := original767.toContract.get (by decide)
theorem binding767 : original767.toContract = some c767 := rfl

theorem checked767 : check 4000 c767 = true := by decide

def original768 : RawOriginal := C006.records[0]'(by decide)
theorem original_id768 : original768.index = 768 := by decide

def c768 : Contract := original768.toContract.get (by decide)
theorem binding768 : original768.toContract = some c768 := rfl

theorem checked768 : check 4000 c768 = true := by decide

def original769 : RawOriginal := C006.records[1]'(by decide)
theorem original_id769 : original769.index = 769 := by decide

def c769 : Contract := original769.toContract.get (by decide)
theorem binding769 : original769.toContract = some c769 := rfl

theorem checked769 : check 4000 c769 = true := by decide

def original770 : RawOriginal := C006.records[2]'(by decide)
theorem original_id770 : original770.index = 770 := by decide

def c770 : Contract := original770.toContract.get (by decide)
theorem binding770 : original770.toContract = some c770 := rfl

theorem checked770 : check 4000 c770 = true := by decide

def original771 : RawOriginal := C006.records[3]'(by decide)
theorem original_id771 : original771.index = 771 := by decide

def c771 : Contract := original771.toContract.get (by decide)
theorem binding771 : original771.toContract = some c771 := rfl

theorem checked771 : check 4000 c771 = true := by decide

def original772 : RawOriginal := C006.records[4]'(by decide)
theorem original_id772 : original772.index = 772 := by decide

def c772 : Contract := original772.toContract.get (by decide)
theorem binding772 : original772.toContract = some c772 := rfl

theorem checked772 : check 4000 c772 = true := by decide

def original773 : RawOriginal := C006.records[5]'(by decide)
theorem original_id773 : original773.index = 773 := by decide

def c773 : Contract := original773.toContract.get (by decide)
theorem binding773 : original773.toContract = some c773 := rfl

theorem checked773 : check 4000 c773 = true := by decide

def records : List Certified := [
  ⟨758, c758, 4000, checked758⟩,
  ⟨759, c759, 4000, checked759⟩,
  ⟨760, c760, 4000, checked760⟩,
  ⟨761, c761, 4000, checked761⟩,
  ⟨762, c762, 4000, checked762⟩,
  ⟨763, c763, 4000, checked763⟩,
  ⟨764, c764, 4000, checked764⟩,
  ⟨765, c765, 4000, checked765⟩,
  ⟨766, c766, 4000, checked766⟩,
  ⟨767, c767, 4000, checked767⟩,
  ⟨768, c768, 4000, checked768⟩,
  ⟨769, c769, 4000, checked769⟩,
  ⟨770, c770, 4000, checked770⟩,
  ⟨771, c771, 4000, checked771⟩,
  ⟨772, c772, 4000, checked772⟩,
  ⟨773, c773, 4000, checked773⟩]

end PA215.ContractShards.Shard005Part7
