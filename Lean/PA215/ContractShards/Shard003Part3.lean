import PA215.CertifiedContracts
import PA215.Census.C003
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard003Part3
open PA215.Contracts PA215.Census

def original438 : RawOriginal := C003.records[54]'(by decide)
theorem original_id438 : original438.index = 438 := by decide

def c438 : Contract := original438.toContract.get (by decide)
theorem binding438 : original438.toContract = some c438 := rfl

theorem checked438 : check 4000 c438 = true := by decide

def original439 : RawOriginal := C003.records[55]'(by decide)
theorem original_id439 : original439.index = 439 := by decide

def c439 : Contract := original439.toContract.get (by decide)
theorem binding439 : original439.toContract = some c439 := rfl

theorem checked439 : check 4000 c439 = true := by decide

def original440 : RawOriginal := C003.records[56]'(by decide)
theorem original_id440 : original440.index = 440 := by decide

def c440 : Contract := original440.toContract.get (by decide)
theorem binding440 : original440.toContract = some c440 := rfl

theorem checked440 : check 4000 c440 = true := by decide

def original441 : RawOriginal := C003.records[57]'(by decide)
theorem original_id441 : original441.index = 441 := by decide

def c441 : Contract := original441.toContract.get (by decide)
theorem binding441 : original441.toContract = some c441 := rfl

theorem checked441 : check 4000 c441 = true := by decide

def original442 : RawOriginal := C003.records[58]'(by decide)
theorem original_id442 : original442.index = 442 := by decide

def c442 : Contract := original442.toContract.get (by decide)
theorem binding442 : original442.toContract = some c442 := rfl

theorem checked442 : check 4000 c442 = true := by decide

def original443 : RawOriginal := C003.records[59]'(by decide)
theorem original_id443 : original443.index = 443 := by decide

def c443 : Contract := original443.toContract.get (by decide)
theorem binding443 : original443.toContract = some c443 := rfl

theorem checked443 : check 4000 c443 = true := by decide

def original444 : RawOriginal := C003.records[60]'(by decide)
theorem original_id444 : original444.index = 444 := by decide

def c444 : Contract := original444.toContract.get (by decide)
theorem binding444 : original444.toContract = some c444 := rfl

theorem checked444 : check 4000 c444 = true := by decide

def original445 : RawOriginal := C003.records[61]'(by decide)
theorem original_id445 : original445.index = 445 := by decide

def c445 : Contract := original445.toContract.get (by decide)
theorem binding445 : original445.toContract = some c445 := rfl

theorem checked445 : check 4000 c445 = true := by decide

def original446 : RawOriginal := C003.records[62]'(by decide)
theorem original_id446 : original446.index = 446 := by decide

def c446 : Contract := original446.toContract.get (by decide)
theorem binding446 : original446.toContract = some c446 := rfl

theorem checked446 : check 4000 c446 = true := by decide

def original447 : RawOriginal := C003.records[63]'(by decide)
theorem original_id447 : original447.index = 447 := by decide

def c447 : Contract := original447.toContract.get (by decide)
theorem binding447 : original447.toContract = some c447 := rfl

theorem checked447 : check 4000 c447 = true := by decide

def original448 : RawOriginal := C003.records[64]'(by decide)
theorem original_id448 : original448.index = 448 := by decide

def c448 : Contract := original448.toContract.get (by decide)
theorem binding448 : original448.toContract = some c448 := rfl

theorem checked448 : check 4000 c448 = true := by decide

def original449 : RawOriginal := C003.records[65]'(by decide)
theorem original_id449 : original449.index = 449 := by decide

def c449 : Contract := original449.toContract.get (by decide)
theorem binding449 : original449.toContract = some c449 := rfl

theorem checked449 : check 4000 c449 = true := by decide

def original450 : RawOriginal := C003.records[66]'(by decide)
theorem original_id450 : original450.index = 450 := by decide

def c450 : Contract := original450.toContract.get (by decide)
theorem binding450 : original450.toContract = some c450 := rfl

theorem checked450 : check 4000 c450 = true := by decide

def original451 : RawOriginal := C003.records[67]'(by decide)
theorem original_id451 : original451.index = 451 := by decide

def c451 : Contract := original451.toContract.get (by decide)
theorem binding451 : original451.toContract = some c451 := rfl

theorem checked451 : check 4000 c451 = true := by decide

def original452 : RawOriginal := C003.records[68]'(by decide)
theorem original_id452 : original452.index = 452 := by decide

def c452 : Contract := original452.toContract.get (by decide)
theorem binding452 : original452.toContract = some c452 := rfl

theorem checked452 : check 4000 c452 = true := by decide

def original453 : RawOriginal := C003.records[69]'(by decide)
theorem original_id453 : original453.index = 453 := by decide

def c453 : Contract := original453.toContract.get (by decide)
theorem binding453 : original453.toContract = some c453 := rfl

theorem checked453 : check 4000 c453 = true := by decide

def records : List Certified := [
  ⟨438, c438, 4000, checked438⟩,
  ⟨439, c439, 4000, checked439⟩,
  ⟨440, c440, 4000, checked440⟩,
  ⟨441, c441, 4000, checked441⟩,
  ⟨442, c442, 4000, checked442⟩,
  ⟨443, c443, 4000, checked443⟩,
  ⟨444, c444, 4000, checked444⟩,
  ⟨445, c445, 4000, checked445⟩,
  ⟨446, c446, 4000, checked446⟩,
  ⟨447, c447, 4000, checked447⟩,
  ⟨448, c448, 4000, checked448⟩,
  ⟨449, c449, 4000, checked449⟩,
  ⟨450, c450, 4000, checked450⟩,
  ⟨451, c451, 4000, checked451⟩,
  ⟨452, c452, 4000, checked452⟩,
  ⟨453, c453, 4000, checked453⟩]

end PA215.ContractShards.Shard003Part3
