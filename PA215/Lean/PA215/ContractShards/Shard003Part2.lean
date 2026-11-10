import PA215.CertifiedContracts
import PA215.Census.C003
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard003Part2
open PA215.Contracts PA215.Census

def original422 : RawOriginal := C003.records[38]'(by decide)
theorem original_id422 : original422.index = 422 := by decide

def c422 : Contract := original422.toContract.get (by decide)
theorem binding422 : original422.toContract = some c422 := rfl

theorem checked422 : check 4000 c422 = true := by decide

def original423 : RawOriginal := C003.records[39]'(by decide)
theorem original_id423 : original423.index = 423 := by decide

def c423 : Contract := original423.toContract.get (by decide)
theorem binding423 : original423.toContract = some c423 := rfl

theorem checked423 : check 4000 c423 = true := by decide

def original424 : RawOriginal := C003.records[40]'(by decide)
theorem original_id424 : original424.index = 424 := by decide

def c424 : Contract := original424.toContract.get (by decide)
theorem binding424 : original424.toContract = some c424 := rfl

theorem checked424 : check 4000 c424 = true := by decide

def original425 : RawOriginal := C003.records[41]'(by decide)
theorem original_id425 : original425.index = 425 := by decide

def c425 : Contract := original425.toContract.get (by decide)
theorem binding425 : original425.toContract = some c425 := rfl

theorem checked425 : check 4000 c425 = true := by decide

def original426 : RawOriginal := C003.records[42]'(by decide)
theorem original_id426 : original426.index = 426 := by decide

def c426 : Contract := original426.toContract.get (by decide)
theorem binding426 : original426.toContract = some c426 := rfl

theorem checked426 : check 4000 c426 = true := by decide

def original427 : RawOriginal := C003.records[43]'(by decide)
theorem original_id427 : original427.index = 427 := by decide

def c427 : Contract := original427.toContract.get (by decide)
theorem binding427 : original427.toContract = some c427 := rfl

theorem checked427 : check 4000 c427 = true := by decide

def original428 : RawOriginal := C003.records[44]'(by decide)
theorem original_id428 : original428.index = 428 := by decide

def c428 : Contract := original428.toContract.get (by decide)
theorem binding428 : original428.toContract = some c428 := rfl

theorem checked428 : check 4000 c428 = true := by decide

def original429 : RawOriginal := C003.records[45]'(by decide)
theorem original_id429 : original429.index = 429 := by decide

def c429 : Contract := original429.toContract.get (by decide)
theorem binding429 : original429.toContract = some c429 := rfl

theorem checked429 : check 4000 c429 = true := by decide

def original430 : RawOriginal := C003.records[46]'(by decide)
theorem original_id430 : original430.index = 430 := by decide

def c430 : Contract := original430.toContract.get (by decide)
theorem binding430 : original430.toContract = some c430 := rfl

theorem checked430 : check 4000 c430 = true := by decide

def original431 : RawOriginal := C003.records[47]'(by decide)
theorem original_id431 : original431.index = 431 := by decide

def c431 : Contract := original431.toContract.get (by decide)
theorem binding431 : original431.toContract = some c431 := rfl

theorem checked431 : check 4000 c431 = true := by decide

def original432 : RawOriginal := C003.records[48]'(by decide)
theorem original_id432 : original432.index = 432 := by decide

def c432 : Contract := original432.toContract.get (by decide)
theorem binding432 : original432.toContract = some c432 := rfl

theorem checked432 : check 4000 c432 = true := by decide

def original433 : RawOriginal := C003.records[49]'(by decide)
theorem original_id433 : original433.index = 433 := by decide

def c433 : Contract := original433.toContract.get (by decide)
theorem binding433 : original433.toContract = some c433 := rfl

theorem checked433 : check 4000 c433 = true := by decide

def original434 : RawOriginal := C003.records[50]'(by decide)
theorem original_id434 : original434.index = 434 := by decide

def c434 : Contract := original434.toContract.get (by decide)
theorem binding434 : original434.toContract = some c434 := rfl

theorem checked434 : check 4000 c434 = true := by decide

def original435 : RawOriginal := C003.records[51]'(by decide)
theorem original_id435 : original435.index = 435 := by decide

def c435 : Contract := original435.toContract.get (by decide)
theorem binding435 : original435.toContract = some c435 := rfl

theorem checked435 : check 4000 c435 = true := by decide

def original436 : RawOriginal := C003.records[52]'(by decide)
theorem original_id436 : original436.index = 436 := by decide

def c436 : Contract := original436.toContract.get (by decide)
theorem binding436 : original436.toContract = some c436 := rfl

theorem checked436 : check 4000 c436 = true := by decide

def original437 : RawOriginal := C003.records[53]'(by decide)
theorem original_id437 : original437.index = 437 := by decide

def c437 : Contract := original437.toContract.get (by decide)
theorem binding437 : original437.toContract = some c437 := rfl

theorem checked437 : check 4000 c437 = true := by decide

def records : List Certified := [
  ⟨422, c422, 4000, checked422⟩,
  ⟨423, c423, 4000, checked423⟩,
  ⟨424, c424, 4000, checked424⟩,
  ⟨425, c425, 4000, checked425⟩,
  ⟨426, c426, 4000, checked426⟩,
  ⟨427, c427, 4000, checked427⟩,
  ⟨428, c428, 4000, checked428⟩,
  ⟨429, c429, 4000, checked429⟩,
  ⟨430, c430, 4000, checked430⟩,
  ⟨431, c431, 4000, checked431⟩,
  ⟨432, c432, 4000, checked432⟩,
  ⟨433, c433, 4000, checked433⟩,
  ⟨434, c434, 4000, checked434⟩,
  ⟨435, c435, 4000, checked435⟩,
  ⟨436, c436, 4000, checked436⟩,
  ⟨437, c437, 4000, checked437⟩]

end PA215.ContractShards.Shard003Part2
