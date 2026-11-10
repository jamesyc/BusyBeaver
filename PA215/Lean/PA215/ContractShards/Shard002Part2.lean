import PA215.CertifiedContracts
import PA215.Census.C002
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard002Part2
open PA215.Contracts PA215.Census

def original294 : RawOriginal := C002.records[38]'(by decide)
theorem original_id294 : original294.index = 294 := by decide

def c294 : Contract := original294.toContract.get (by decide)
theorem binding294 : original294.toContract = some c294 := rfl

theorem checked294 : check 4000 c294 = true := by decide

def original295 : RawOriginal := C002.records[39]'(by decide)
theorem original_id295 : original295.index = 295 := by decide

def c295 : Contract := original295.toContract.get (by decide)
theorem binding295 : original295.toContract = some c295 := rfl

theorem checked295 : check 4000 c295 = true := by decide

def original296 : RawOriginal := C002.records[40]'(by decide)
theorem original_id296 : original296.index = 296 := by decide

def c296 : Contract := original296.toContract.get (by decide)
theorem binding296 : original296.toContract = some c296 := rfl

theorem checked296 : check 4000 c296 = true := by decide

def original297 : RawOriginal := C002.records[41]'(by decide)
theorem original_id297 : original297.index = 297 := by decide

def c297 : Contract := original297.toContract.get (by decide)
theorem binding297 : original297.toContract = some c297 := rfl

theorem checked297 : check 4000 c297 = true := by decide

def original298 : RawOriginal := C002.records[42]'(by decide)
theorem original_id298 : original298.index = 298 := by decide

def c298 : Contract := original298.toContract.get (by decide)
theorem binding298 : original298.toContract = some c298 := rfl

theorem checked298 : check 4000 c298 = true := by decide

def original299 : RawOriginal := C002.records[43]'(by decide)
theorem original_id299 : original299.index = 299 := by decide

def c299 : Contract := original299.toContract.get (by decide)
theorem binding299 : original299.toContract = some c299 := rfl

theorem checked299 : check 4000 c299 = true := by decide

def original300 : RawOriginal := C002.records[44]'(by decide)
theorem original_id300 : original300.index = 300 := by decide

def c300 : Contract := original300.toContract.get (by decide)
theorem binding300 : original300.toContract = some c300 := rfl

theorem checked300 : check 4000 c300 = true := by decide

def original301 : RawOriginal := C002.records[45]'(by decide)
theorem original_id301 : original301.index = 301 := by decide

def c301 : Contract := original301.toContract.get (by decide)
theorem binding301 : original301.toContract = some c301 := rfl

theorem checked301 : check 4000 c301 = true := by decide

def original302 : RawOriginal := C002.records[46]'(by decide)
theorem original_id302 : original302.index = 302 := by decide

def c302 : Contract := original302.toContract.get (by decide)
theorem binding302 : original302.toContract = some c302 := rfl

theorem checked302 : check 4000 c302 = true := by decide

def original303 : RawOriginal := C002.records[47]'(by decide)
theorem original_id303 : original303.index = 303 := by decide

def c303 : Contract := original303.toContract.get (by decide)
theorem binding303 : original303.toContract = some c303 := rfl

theorem checked303 : check 4000 c303 = true := by decide

def original304 : RawOriginal := C002.records[48]'(by decide)
theorem original_id304 : original304.index = 304 := by decide

def c304 : Contract := original304.toContract.get (by decide)
theorem binding304 : original304.toContract = some c304 := rfl

theorem checked304 : check 4000 c304 = true := by decide

def original305 : RawOriginal := C002.records[49]'(by decide)
theorem original_id305 : original305.index = 305 := by decide

def c305 : Contract := original305.toContract.get (by decide)
theorem binding305 : original305.toContract = some c305 := rfl

theorem checked305 : check 4000 c305 = true := by decide

def original306 : RawOriginal := C002.records[50]'(by decide)
theorem original_id306 : original306.index = 306 := by decide

def c306 : Contract := original306.toContract.get (by decide)
theorem binding306 : original306.toContract = some c306 := rfl

theorem checked306 : check 4000 c306 = true := by decide

def original307 : RawOriginal := C002.records[51]'(by decide)
theorem original_id307 : original307.index = 307 := by decide

def c307 : Contract := original307.toContract.get (by decide)
theorem binding307 : original307.toContract = some c307 := rfl

theorem checked307 : check 4000 c307 = true := by decide

def original308 : RawOriginal := C002.records[52]'(by decide)
theorem original_id308 : original308.index = 308 := by decide

def c308 : Contract := original308.toContract.get (by decide)
theorem binding308 : original308.toContract = some c308 := rfl

theorem checked308 : check 4000 c308 = true := by decide

def original309 : RawOriginal := C002.records[53]'(by decide)
theorem original_id309 : original309.index = 309 := by decide

def c309 : Contract := original309.toContract.get (by decide)
theorem binding309 : original309.toContract = some c309 := rfl

theorem checked309 : check 4000 c309 = true := by decide

def records : List Certified := [
  ⟨294, c294, 4000, checked294⟩,
  ⟨295, c295, 4000, checked295⟩,
  ⟨296, c296, 4000, checked296⟩,
  ⟨297, c297, 4000, checked297⟩,
  ⟨298, c298, 4000, checked298⟩,
  ⟨299, c299, 4000, checked299⟩,
  ⟨300, c300, 4000, checked300⟩,
  ⟨301, c301, 4000, checked301⟩,
  ⟨302, c302, 4000, checked302⟩,
  ⟨303, c303, 4000, checked303⟩,
  ⟨304, c304, 4000, checked304⟩,
  ⟨305, c305, 4000, checked305⟩,
  ⟨306, c306, 4000, checked306⟩,
  ⟨307, c307, 4000, checked307⟩,
  ⟨308, c308, 4000, checked308⟩,
  ⟨309, c309, 4000, checked309⟩]

end PA215.ContractShards.Shard002Part2
