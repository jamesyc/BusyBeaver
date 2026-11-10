import PA215.CertifiedContracts
import PA215.Census.C002
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard002Part1
open PA215.Contracts PA215.Census

def original278 : RawOriginal := C002.records[22]'(by decide)
theorem original_id278 : original278.index = 278 := by decide

def c278 : Contract := original278.toContract.get (by decide)
theorem binding278 : original278.toContract = some c278 := rfl

theorem checked278 : check 4000 c278 = true := by decide

def original279 : RawOriginal := C002.records[23]'(by decide)
theorem original_id279 : original279.index = 279 := by decide

def c279 : Contract := original279.toContract.get (by decide)
theorem binding279 : original279.toContract = some c279 := rfl

theorem checked279 : check 4000 c279 = true := by decide

def original280 : RawOriginal := C002.records[24]'(by decide)
theorem original_id280 : original280.index = 280 := by decide

def c280 : Contract := original280.toContract.get (by decide)
theorem binding280 : original280.toContract = some c280 := rfl

theorem checked280 : check 4000 c280 = true := by decide

def original281 : RawOriginal := C002.records[25]'(by decide)
theorem original_id281 : original281.index = 281 := by decide

def c281 : Contract := original281.toContract.get (by decide)
theorem binding281 : original281.toContract = some c281 := rfl

theorem checked281 : check 4000 c281 = true := by decide

def original282 : RawOriginal := C002.records[26]'(by decide)
theorem original_id282 : original282.index = 282 := by decide

def c282 : Contract := original282.toContract.get (by decide)
theorem binding282 : original282.toContract = some c282 := rfl

theorem checked282 : check 4000 c282 = true := by decide

def original283 : RawOriginal := C002.records[27]'(by decide)
theorem original_id283 : original283.index = 283 := by decide

def c283 : Contract := original283.toContract.get (by decide)
theorem binding283 : original283.toContract = some c283 := rfl

theorem checked283 : check 4000 c283 = true := by decide

def original284 : RawOriginal := C002.records[28]'(by decide)
theorem original_id284 : original284.index = 284 := by decide

def c284 : Contract := original284.toContract.get (by decide)
theorem binding284 : original284.toContract = some c284 := rfl

theorem checked284 : check 4000 c284 = true := by decide

def original285 : RawOriginal := C002.records[29]'(by decide)
theorem original_id285 : original285.index = 285 := by decide

def c285 : Contract := original285.toContract.get (by decide)
theorem binding285 : original285.toContract = some c285 := rfl

theorem checked285 : check 4000 c285 = true := by decide

def original286 : RawOriginal := C002.records[30]'(by decide)
theorem original_id286 : original286.index = 286 := by decide

def c286 : Contract := original286.toContract.get (by decide)
theorem binding286 : original286.toContract = some c286 := rfl

theorem checked286 : check 4000 c286 = true := by decide

def original287 : RawOriginal := C002.records[31]'(by decide)
theorem original_id287 : original287.index = 287 := by decide

def c287 : Contract := original287.toContract.get (by decide)
theorem binding287 : original287.toContract = some c287 := rfl

theorem checked287 : check 4000 c287 = true := by decide

def original288 : RawOriginal := C002.records[32]'(by decide)
theorem original_id288 : original288.index = 288 := by decide

def c288 : Contract := original288.toContract.get (by decide)
theorem binding288 : original288.toContract = some c288 := rfl

theorem checked288 : check 4000 c288 = true := by decide

def original289 : RawOriginal := C002.records[33]'(by decide)
theorem original_id289 : original289.index = 289 := by decide

def c289 : Contract := original289.toContract.get (by decide)
theorem binding289 : original289.toContract = some c289 := rfl

theorem checked289 : check 4000 c289 = true := by decide

def original290 : RawOriginal := C002.records[34]'(by decide)
theorem original_id290 : original290.index = 290 := by decide

def c290 : Contract := original290.toContract.get (by decide)
theorem binding290 : original290.toContract = some c290 := rfl

theorem checked290 : check 4000 c290 = true := by decide

def original291 : RawOriginal := C002.records[35]'(by decide)
theorem original_id291 : original291.index = 291 := by decide

def c291 : Contract := original291.toContract.get (by decide)
theorem binding291 : original291.toContract = some c291 := rfl

theorem checked291 : check 4000 c291 = true := by decide

def original292 : RawOriginal := C002.records[36]'(by decide)
theorem original_id292 : original292.index = 292 := by decide

def c292 : Contract := original292.toContract.get (by decide)
theorem binding292 : original292.toContract = some c292 := rfl

theorem checked292 : check 4000 c292 = true := by decide

def original293 : RawOriginal := C002.records[37]'(by decide)
theorem original_id293 : original293.index = 293 := by decide

def c293 : Contract := original293.toContract.get (by decide)
theorem binding293 : original293.toContract = some c293 := rfl

theorem checked293 : check 4000 c293 = true := by decide

def records : List Certified := [
  ⟨278, c278, 4000, checked278⟩,
  ⟨279, c279, 4000, checked279⟩,
  ⟨280, c280, 4000, checked280⟩,
  ⟨281, c281, 4000, checked281⟩,
  ⟨282, c282, 4000, checked282⟩,
  ⟨283, c283, 4000, checked283⟩,
  ⟨284, c284, 4000, checked284⟩,
  ⟨285, c285, 4000, checked285⟩,
  ⟨286, c286, 4000, checked286⟩,
  ⟨287, c287, 4000, checked287⟩,
  ⟨288, c288, 4000, checked288⟩,
  ⟨289, c289, 4000, checked289⟩,
  ⟨290, c290, 4000, checked290⟩,
  ⟨291, c291, 4000, checked291⟩,
  ⟨292, c292, 4000, checked292⟩,
  ⟨293, c293, 4000, checked293⟩]

end PA215.ContractShards.Shard002Part1
