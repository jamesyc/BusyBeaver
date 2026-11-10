import PA215.CertifiedContracts
import PA215.Census.C001
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard001Part6
open PA215.Contracts PA215.Census

def original230 : RawOriginal := C001.records[102]'(by decide)
theorem original_id230 : original230.index = 230 := by decide

def c230 : Contract := original230.toContract.get (by decide)
theorem binding230 : original230.toContract = some c230 := rfl

theorem checked230 : check 4000 c230 = true := by decide

def original231 : RawOriginal := C001.records[103]'(by decide)
theorem original_id231 : original231.index = 231 := by decide

def c231 : Contract := original231.toContract.get (by decide)
theorem binding231 : original231.toContract = some c231 := rfl

theorem checked231 : check 4000 c231 = true := by decide

def original232 : RawOriginal := C001.records[104]'(by decide)
theorem original_id232 : original232.index = 232 := by decide

def c232 : Contract := original232.toContract.get (by decide)
theorem binding232 : original232.toContract = some c232 := rfl

theorem checked232 : check 4000 c232 = true := by decide

def original233 : RawOriginal := C001.records[105]'(by decide)
theorem original_id233 : original233.index = 233 := by decide

def c233 : Contract := original233.toContract.get (by decide)
theorem binding233 : original233.toContract = some c233 := rfl

theorem checked233 : check 4000 c233 = true := by decide

def original234 : RawOriginal := C001.records[106]'(by decide)
theorem original_id234 : original234.index = 234 := by decide

def c234 : Contract := original234.toContract.get (by decide)
theorem binding234 : original234.toContract = some c234 := rfl

theorem checked234 : check 4000 c234 = true := by decide

def original235 : RawOriginal := C001.records[107]'(by decide)
theorem original_id235 : original235.index = 235 := by decide

def c235 : Contract := original235.toContract.get (by decide)
theorem binding235 : original235.toContract = some c235 := rfl

theorem checked235 : check 4000 c235 = true := by decide

def original236 : RawOriginal := C001.records[108]'(by decide)
theorem original_id236 : original236.index = 236 := by decide

def c236 : Contract := original236.toContract.get (by decide)
theorem binding236 : original236.toContract = some c236 := rfl

theorem checked236 : check 4000 c236 = true := by decide

def original237 : RawOriginal := C001.records[109]'(by decide)
theorem original_id237 : original237.index = 237 := by decide

def c237 : Contract := original237.toContract.get (by decide)
theorem binding237 : original237.toContract = some c237 := rfl

theorem checked237 : check 4000 c237 = true := by decide

def original238 : RawOriginal := C001.records[110]'(by decide)
theorem original_id238 : original238.index = 238 := by decide

def c238 : Contract := original238.toContract.get (by decide)
theorem binding238 : original238.toContract = some c238 := rfl

theorem checked238 : check 4000 c238 = true := by decide

def original239 : RawOriginal := C001.records[111]'(by decide)
theorem original_id239 : original239.index = 239 := by decide

def c239 : Contract := original239.toContract.get (by decide)
theorem binding239 : original239.toContract = some c239 := rfl

theorem checked239 : check 4000 c239 = true := by decide

def original240 : RawOriginal := C001.records[112]'(by decide)
theorem original_id240 : original240.index = 240 := by decide

def c240 : Contract := original240.toContract.get (by decide)
theorem binding240 : original240.toContract = some c240 := rfl

theorem checked240 : check 4000 c240 = true := by decide

def original241 : RawOriginal := C001.records[113]'(by decide)
theorem original_id241 : original241.index = 241 := by decide

def c241 : Contract := original241.toContract.get (by decide)
theorem binding241 : original241.toContract = some c241 := rfl

theorem checked241 : check 4000 c241 = true := by decide

def original242 : RawOriginal := C001.records[114]'(by decide)
theorem original_id242 : original242.index = 242 := by decide

def c242 : Contract := original242.toContract.get (by decide)
theorem binding242 : original242.toContract = some c242 := rfl

theorem checked242 : check 4000 c242 = true := by decide

def original243 : RawOriginal := C001.records[115]'(by decide)
theorem original_id243 : original243.index = 243 := by decide

def c243 : Contract := original243.toContract.get (by decide)
theorem binding243 : original243.toContract = some c243 := rfl

theorem checked243 : check 4000 c243 = true := by decide

def original244 : RawOriginal := C001.records[116]'(by decide)
theorem original_id244 : original244.index = 244 := by decide

def c244 : Contract := original244.toContract.get (by decide)
theorem binding244 : original244.toContract = some c244 := rfl

theorem checked244 : check 4000 c244 = true := by decide

def original245 : RawOriginal := C001.records[117]'(by decide)
theorem original_id245 : original245.index = 245 := by decide

def c245 : Contract := original245.toContract.get (by decide)
theorem binding245 : original245.toContract = some c245 := rfl

theorem checked245 : check 4000 c245 = true := by decide

def records : List Certified := [
  ⟨230, c230, 4000, checked230⟩,
  ⟨231, c231, 4000, checked231⟩,
  ⟨232, c232, 4000, checked232⟩,
  ⟨233, c233, 4000, checked233⟩,
  ⟨234, c234, 4000, checked234⟩,
  ⟨235, c235, 4000, checked235⟩,
  ⟨236, c236, 4000, checked236⟩,
  ⟨237, c237, 4000, checked237⟩,
  ⟨238, c238, 4000, checked238⟩,
  ⟨239, c239, 4000, checked239⟩,
  ⟨240, c240, 4000, checked240⟩,
  ⟨241, c241, 4000, checked241⟩,
  ⟨242, c242, 4000, checked242⟩,
  ⟨243, c243, 4000, checked243⟩,
  ⟨244, c244, 4000, checked244⟩,
  ⟨245, c245, 4000, checked245⟩]

end PA215.ContractShards.Shard001Part6
