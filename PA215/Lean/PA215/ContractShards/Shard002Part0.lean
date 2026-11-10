import PA215.CertifiedContracts
import PA215.Census.C002
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard002Part0
open PA215.Contracts PA215.Census

def original262 : RawOriginal := C002.records[6]'(by decide)
theorem original_id262 : original262.index = 262 := by decide

def c262 : Contract := original262.toContract.get (by decide)
theorem binding262 : original262.toContract = some c262 := rfl

theorem checked262 : check 4000 c262 = true := by decide

def original263 : RawOriginal := C002.records[7]'(by decide)
theorem original_id263 : original263.index = 263 := by decide

def c263 : Contract := original263.toContract.get (by decide)
theorem binding263 : original263.toContract = some c263 := rfl

theorem checked263 : check 4000 c263 = true := by decide

def original264 : RawOriginal := C002.records[8]'(by decide)
theorem original_id264 : original264.index = 264 := by decide

def c264 : Contract := original264.toContract.get (by decide)
theorem binding264 : original264.toContract = some c264 := rfl

theorem checked264 : check 4000 c264 = true := by decide

def original265 : RawOriginal := C002.records[9]'(by decide)
theorem original_id265 : original265.index = 265 := by decide

def c265 : Contract := original265.toContract.get (by decide)
theorem binding265 : original265.toContract = some c265 := rfl

theorem checked265 : check 4000 c265 = true := by decide

def original266 : RawOriginal := C002.records[10]'(by decide)
theorem original_id266 : original266.index = 266 := by decide

def c266 : Contract := original266.toContract.get (by decide)
theorem binding266 : original266.toContract = some c266 := rfl

theorem checked266 : check 4000 c266 = true := by decide

def original267 : RawOriginal := C002.records[11]'(by decide)
theorem original_id267 : original267.index = 267 := by decide

def c267 : Contract := original267.toContract.get (by decide)
theorem binding267 : original267.toContract = some c267 := rfl

theorem checked267 : check 4000 c267 = true := by decide

def original268 : RawOriginal := C002.records[12]'(by decide)
theorem original_id268 : original268.index = 268 := by decide

def c268 : Contract := original268.toContract.get (by decide)
theorem binding268 : original268.toContract = some c268 := rfl

theorem checked268 : check 4000 c268 = true := by decide

def original269 : RawOriginal := C002.records[13]'(by decide)
theorem original_id269 : original269.index = 269 := by decide

def c269 : Contract := original269.toContract.get (by decide)
theorem binding269 : original269.toContract = some c269 := rfl

theorem checked269 : check 4000 c269 = true := by decide

def original270 : RawOriginal := C002.records[14]'(by decide)
theorem original_id270 : original270.index = 270 := by decide

def c270 : Contract := original270.toContract.get (by decide)
theorem binding270 : original270.toContract = some c270 := rfl

theorem checked270 : check 4000 c270 = true := by decide

def original271 : RawOriginal := C002.records[15]'(by decide)
theorem original_id271 : original271.index = 271 := by decide

def c271 : Contract := original271.toContract.get (by decide)
theorem binding271 : original271.toContract = some c271 := rfl

theorem checked271 : check 4000 c271 = true := by decide

def original272 : RawOriginal := C002.records[16]'(by decide)
theorem original_id272 : original272.index = 272 := by decide

def c272 : Contract := original272.toContract.get (by decide)
theorem binding272 : original272.toContract = some c272 := rfl

theorem checked272 : check 4000 c272 = true := by decide

def original273 : RawOriginal := C002.records[17]'(by decide)
theorem original_id273 : original273.index = 273 := by decide

def c273 : Contract := original273.toContract.get (by decide)
theorem binding273 : original273.toContract = some c273 := rfl

theorem checked273 : check 4000 c273 = true := by decide

def original274 : RawOriginal := C002.records[18]'(by decide)
theorem original_id274 : original274.index = 274 := by decide

def c274 : Contract := original274.toContract.get (by decide)
theorem binding274 : original274.toContract = some c274 := rfl

theorem checked274 : check 4000 c274 = true := by decide

def original275 : RawOriginal := C002.records[19]'(by decide)
theorem original_id275 : original275.index = 275 := by decide

def c275 : Contract := original275.toContract.get (by decide)
theorem binding275 : original275.toContract = some c275 := rfl

theorem checked275 : check 4000 c275 = true := by decide

def original276 : RawOriginal := C002.records[20]'(by decide)
theorem original_id276 : original276.index = 276 := by decide

def c276 : Contract := original276.toContract.get (by decide)
theorem binding276 : original276.toContract = some c276 := rfl

theorem checked276 : check 4000 c276 = true := by decide

def original277 : RawOriginal := C002.records[21]'(by decide)
theorem original_id277 : original277.index = 277 := by decide

def c277 : Contract := original277.toContract.get (by decide)
theorem binding277 : original277.toContract = some c277 := rfl

theorem checked277 : check 4000 c277 = true := by decide

def records : List Certified := [
  ⟨262, c262, 4000, checked262⟩,
  ⟨263, c263, 4000, checked263⟩,
  ⟨264, c264, 4000, checked264⟩,
  ⟨265, c265, 4000, checked265⟩,
  ⟨266, c266, 4000, checked266⟩,
  ⟨267, c267, 4000, checked267⟩,
  ⟨268, c268, 4000, checked268⟩,
  ⟨269, c269, 4000, checked269⟩,
  ⟨270, c270, 4000, checked270⟩,
  ⟨271, c271, 4000, checked271⟩,
  ⟨272, c272, 4000, checked272⟩,
  ⟨273, c273, 4000, checked273⟩,
  ⟨274, c274, 4000, checked274⟩,
  ⟨275, c275, 4000, checked275⟩,
  ⟨276, c276, 4000, checked276⟩,
  ⟨277, c277, 4000, checked277⟩]

end PA215.ContractShards.Shard002Part0
