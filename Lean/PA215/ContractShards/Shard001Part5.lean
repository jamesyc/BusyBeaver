import PA215.CertifiedContracts
import PA215.Census.C001
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard001Part5
open PA215.Contracts PA215.Census

def original214 : RawOriginal := C001.records[86]'(by decide)
theorem original_id214 : original214.index = 214 := by decide

def c214 : Contract := original214.toContract.get (by decide)
theorem binding214 : original214.toContract = some c214 := rfl

theorem checked214 : check 4000 c214 = true := by decide

def original215 : RawOriginal := C001.records[87]'(by decide)
theorem original_id215 : original215.index = 215 := by decide

def c215 : Contract := original215.toContract.get (by decide)
theorem binding215 : original215.toContract = some c215 := rfl

theorem checked215 : check 4000 c215 = true := by decide

def original216 : RawOriginal := C001.records[88]'(by decide)
theorem original_id216 : original216.index = 216 := by decide

def c216 : Contract := original216.toContract.get (by decide)
theorem binding216 : original216.toContract = some c216 := rfl

theorem checked216 : check 4000 c216 = true := by decide

def original217 : RawOriginal := C001.records[89]'(by decide)
theorem original_id217 : original217.index = 217 := by decide

def c217 : Contract := original217.toContract.get (by decide)
theorem binding217 : original217.toContract = some c217 := rfl

theorem checked217 : check 4000 c217 = true := by decide

def original218 : RawOriginal := C001.records[90]'(by decide)
theorem original_id218 : original218.index = 218 := by decide

def c218 : Contract := original218.toContract.get (by decide)
theorem binding218 : original218.toContract = some c218 := rfl

theorem checked218 : check 4000 c218 = true := by decide

def original219 : RawOriginal := C001.records[91]'(by decide)
theorem original_id219 : original219.index = 219 := by decide

def c219 : Contract := original219.toContract.get (by decide)
theorem binding219 : original219.toContract = some c219 := rfl

theorem checked219 : check 4000 c219 = true := by decide

def original220 : RawOriginal := C001.records[92]'(by decide)
theorem original_id220 : original220.index = 220 := by decide

def c220 : Contract := original220.toContract.get (by decide)
theorem binding220 : original220.toContract = some c220 := rfl

theorem checked220 : check 4000 c220 = true := by decide

def original221 : RawOriginal := C001.records[93]'(by decide)
theorem original_id221 : original221.index = 221 := by decide

def c221 : Contract := original221.toContract.get (by decide)
theorem binding221 : original221.toContract = some c221 := rfl

theorem checked221 : check 4000 c221 = true := by decide

def original222 : RawOriginal := C001.records[94]'(by decide)
theorem original_id222 : original222.index = 222 := by decide

def c222 : Contract := original222.toContract.get (by decide)
theorem binding222 : original222.toContract = some c222 := rfl

theorem checked222 : check 4000 c222 = true := by decide

def original223 : RawOriginal := C001.records[95]'(by decide)
theorem original_id223 : original223.index = 223 := by decide

def c223 : Contract := original223.toContract.get (by decide)
theorem binding223 : original223.toContract = some c223 := rfl

theorem checked223 : check 4000 c223 = true := by decide

def original224 : RawOriginal := C001.records[96]'(by decide)
theorem original_id224 : original224.index = 224 := by decide

def c224 : Contract := original224.toContract.get (by decide)
theorem binding224 : original224.toContract = some c224 := rfl

theorem checked224 : check 4000 c224 = true := by decide

def original225 : RawOriginal := C001.records[97]'(by decide)
theorem original_id225 : original225.index = 225 := by decide

def c225 : Contract := original225.toContract.get (by decide)
theorem binding225 : original225.toContract = some c225 := rfl

theorem checked225 : check 4000 c225 = true := by decide

def original226 : RawOriginal := C001.records[98]'(by decide)
theorem original_id226 : original226.index = 226 := by decide

def c226 : Contract := original226.toContract.get (by decide)
theorem binding226 : original226.toContract = some c226 := rfl

theorem checked226 : check 4000 c226 = true := by decide

def original227 : RawOriginal := C001.records[99]'(by decide)
theorem original_id227 : original227.index = 227 := by decide

def c227 : Contract := original227.toContract.get (by decide)
theorem binding227 : original227.toContract = some c227 := rfl

theorem checked227 : check 4000 c227 = true := by decide

def original228 : RawOriginal := C001.records[100]'(by decide)
theorem original_id228 : original228.index = 228 := by decide

def c228 : Contract := original228.toContract.get (by decide)
theorem binding228 : original228.toContract = some c228 := rfl

theorem checked228 : check 4000 c228 = true := by decide

def original229 : RawOriginal := C001.records[101]'(by decide)
theorem original_id229 : original229.index = 229 := by decide

def c229 : Contract := original229.toContract.get (by decide)
theorem binding229 : original229.toContract = some c229 := rfl

theorem checked229 : check 4000 c229 = true := by decide

def records : List Certified := [
  ⟨214, c214, 4000, checked214⟩,
  ⟨215, c215, 4000, checked215⟩,
  ⟨216, c216, 4000, checked216⟩,
  ⟨217, c217, 4000, checked217⟩,
  ⟨218, c218, 4000, checked218⟩,
  ⟨219, c219, 4000, checked219⟩,
  ⟨220, c220, 4000, checked220⟩,
  ⟨221, c221, 4000, checked221⟩,
  ⟨222, c222, 4000, checked222⟩,
  ⟨223, c223, 4000, checked223⟩,
  ⟨224, c224, 4000, checked224⟩,
  ⟨225, c225, 4000, checked225⟩,
  ⟨226, c226, 4000, checked226⟩,
  ⟨227, c227, 4000, checked227⟩,
  ⟨228, c228, 4000, checked228⟩,
  ⟨229, c229, 4000, checked229⟩]

end PA215.ContractShards.Shard001Part5
