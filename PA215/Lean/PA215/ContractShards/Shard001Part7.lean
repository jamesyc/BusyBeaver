import PA215.CertifiedContracts
import PA215.Census.C001
import PA215.Census.C002
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard001Part7
open PA215.Contracts PA215.Census

def original246 : RawOriginal := C001.records[118]'(by decide)
theorem original_id246 : original246.index = 246 := by decide

def c246 : Contract := original246.toContract.get (by decide)
theorem binding246 : original246.toContract = some c246 := rfl

theorem checked246 : check 4000 c246 = true := by decide

def original247 : RawOriginal := C001.records[119]'(by decide)
theorem original_id247 : original247.index = 247 := by decide

def c247 : Contract := original247.toContract.get (by decide)
theorem binding247 : original247.toContract = some c247 := rfl

theorem checked247 : check 4000 c247 = true := by decide

def original248 : RawOriginal := C001.records[120]'(by decide)
theorem original_id248 : original248.index = 248 := by decide

def c248 : Contract := original248.toContract.get (by decide)
theorem binding248 : original248.toContract = some c248 := rfl

theorem checked248 : check 4000 c248 = true := by decide

def original249 : RawOriginal := C001.records[121]'(by decide)
theorem original_id249 : original249.index = 249 := by decide

def c249 : Contract := original249.toContract.get (by decide)
theorem binding249 : original249.toContract = some c249 := rfl

theorem checked249 : check 4000 c249 = true := by decide

def original250 : RawOriginal := C001.records[122]'(by decide)
theorem original_id250 : original250.index = 250 := by decide

def c250 : Contract := original250.toContract.get (by decide)
theorem binding250 : original250.toContract = some c250 := rfl

theorem checked250 : check 4000 c250 = true := by decide

def original251 : RawOriginal := C001.records[123]'(by decide)
theorem original_id251 : original251.index = 251 := by decide

def c251 : Contract := original251.toContract.get (by decide)
theorem binding251 : original251.toContract = some c251 := rfl

theorem checked251 : check 4000 c251 = true := by decide

def original252 : RawOriginal := C001.records[124]'(by decide)
theorem original_id252 : original252.index = 252 := by decide

def c252 : Contract := original252.toContract.get (by decide)
theorem binding252 : original252.toContract = some c252 := rfl

theorem checked252 : check 4000 c252 = true := by decide

def original253 : RawOriginal := C001.records[125]'(by decide)
theorem original_id253 : original253.index = 253 := by decide

def c253 : Contract := original253.toContract.get (by decide)
theorem binding253 : original253.toContract = some c253 := rfl

theorem checked253 : check 4000 c253 = true := by decide

def original254 : RawOriginal := C001.records[126]'(by decide)
theorem original_id254 : original254.index = 254 := by decide

def c254 : Contract := original254.toContract.get (by decide)
theorem binding254 : original254.toContract = some c254 := rfl

theorem checked254 : check 4000 c254 = true := by decide

def original255 : RawOriginal := C001.records[127]'(by decide)
theorem original_id255 : original255.index = 255 := by decide

def c255 : Contract := original255.toContract.get (by decide)
theorem binding255 : original255.toContract = some c255 := rfl

theorem checked255 : check 4000 c255 = true := by decide

def original256 : RawOriginal := C002.records[0]'(by decide)
theorem original_id256 : original256.index = 256 := by decide

def c256 : Contract := original256.toContract.get (by decide)
theorem binding256 : original256.toContract = some c256 := rfl

theorem checked256 : check 4000 c256 = true := by decide

def original257 : RawOriginal := C002.records[1]'(by decide)
theorem original_id257 : original257.index = 257 := by decide

def c257 : Contract := original257.toContract.get (by decide)
theorem binding257 : original257.toContract = some c257 := rfl

theorem checked257 : check 4000 c257 = true := by decide

def original258 : RawOriginal := C002.records[2]'(by decide)
theorem original_id258 : original258.index = 258 := by decide

def c258 : Contract := original258.toContract.get (by decide)
theorem binding258 : original258.toContract = some c258 := rfl

theorem checked258 : check 4000 c258 = true := by decide

def original259 : RawOriginal := C002.records[3]'(by decide)
theorem original_id259 : original259.index = 259 := by decide

def c259 : Contract := original259.toContract.get (by decide)
theorem binding259 : original259.toContract = some c259 := rfl

theorem checked259 : check 4000 c259 = true := by decide

def original260 : RawOriginal := C002.records[4]'(by decide)
theorem original_id260 : original260.index = 260 := by decide

def c260 : Contract := original260.toContract.get (by decide)
theorem binding260 : original260.toContract = some c260 := rfl

theorem checked260 : check 4000 c260 = true := by decide

def original261 : RawOriginal := C002.records[5]'(by decide)
theorem original_id261 : original261.index = 261 := by decide

def c261 : Contract := original261.toContract.get (by decide)
theorem binding261 : original261.toContract = some c261 := rfl

theorem checked261 : check 4000 c261 = true := by decide

def records : List Certified := [
  ⟨246, c246, 4000, checked246⟩,
  ⟨247, c247, 4000, checked247⟩,
  ⟨248, c248, 4000, checked248⟩,
  ⟨249, c249, 4000, checked249⟩,
  ⟨250, c250, 4000, checked250⟩,
  ⟨251, c251, 4000, checked251⟩,
  ⟨252, c252, 4000, checked252⟩,
  ⟨253, c253, 4000, checked253⟩,
  ⟨254, c254, 4000, checked254⟩,
  ⟨255, c255, 4000, checked255⟩,
  ⟨256, c256, 4000, checked256⟩,
  ⟨257, c257, 4000, checked257⟩,
  ⟨258, c258, 4000, checked258⟩,
  ⟨259, c259, 4000, checked259⟩,
  ⟨260, c260, 4000, checked260⟩,
  ⟨261, c261, 4000, checked261⟩]

end PA215.ContractShards.Shard001Part7
