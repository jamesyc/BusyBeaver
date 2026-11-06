import PA215.CertifiedContracts
import PA215.Census.C003
import PA215.Census.C004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard003Part7
open PA215.Contracts PA215.Census

def original502 : RawOriginal := C003.records[118]'(by decide)
theorem original_id502 : original502.index = 502 := by decide

def c502 : Contract := original502.toContract.get (by decide)
theorem binding502 : original502.toContract = some c502 := rfl

theorem checked502 : check 4000 c502 = true := by decide

def original503 : RawOriginal := C003.records[119]'(by decide)
theorem original_id503 : original503.index = 503 := by decide

def c503 : Contract := original503.toContract.get (by decide)
theorem binding503 : original503.toContract = some c503 := rfl

theorem checked503 : check 4000 c503 = true := by decide

def original504 : RawOriginal := C003.records[120]'(by decide)
theorem original_id504 : original504.index = 504 := by decide

def c504 : Contract := original504.toContract.get (by decide)
theorem binding504 : original504.toContract = some c504 := rfl

theorem checked504 : check 4000 c504 = true := by decide

def original505 : RawOriginal := C003.records[121]'(by decide)
theorem original_id505 : original505.index = 505 := by decide

def c505 : Contract := original505.toContract.get (by decide)
theorem binding505 : original505.toContract = some c505 := rfl

theorem checked505 : check 4000 c505 = true := by decide

def original506 : RawOriginal := C003.records[122]'(by decide)
theorem original_id506 : original506.index = 506 := by decide

def c506 : Contract := original506.toContract.get (by decide)
theorem binding506 : original506.toContract = some c506 := rfl

theorem checked506 : check 4000 c506 = true := by decide

def original507 : RawOriginal := C003.records[123]'(by decide)
theorem original_id507 : original507.index = 507 := by decide

def c507 : Contract := original507.toContract.get (by decide)
theorem binding507 : original507.toContract = some c507 := rfl

theorem checked507 : check 4000 c507 = true := by decide

def original508 : RawOriginal := C003.records[124]'(by decide)
theorem original_id508 : original508.index = 508 := by decide

def c508 : Contract := original508.toContract.get (by decide)
theorem binding508 : original508.toContract = some c508 := rfl

theorem checked508 : check 4000 c508 = true := by decide

def original509 : RawOriginal := C003.records[125]'(by decide)
theorem original_id509 : original509.index = 509 := by decide

def c509 : Contract := original509.toContract.get (by decide)
theorem binding509 : original509.toContract = some c509 := rfl

theorem checked509 : check 4000 c509 = true := by decide

def original510 : RawOriginal := C003.records[126]'(by decide)
theorem original_id510 : original510.index = 510 := by decide

def c510 : Contract := original510.toContract.get (by decide)
theorem binding510 : original510.toContract = some c510 := rfl

theorem checked510 : check 4000 c510 = true := by decide

def original511 : RawOriginal := C003.records[127]'(by decide)
theorem original_id511 : original511.index = 511 := by decide

def c511 : Contract := original511.toContract.get (by decide)
theorem binding511 : original511.toContract = some c511 := rfl

theorem checked511 : check 4000 c511 = true := by decide

def original512 : RawOriginal := C004.records[0]'(by decide)
theorem original_id512 : original512.index = 512 := by decide

def c512 : Contract := original512.toContract.get (by decide)
theorem binding512 : original512.toContract = some c512 := rfl

theorem checked512 : check 4000 c512 = true := by decide

def original513 : RawOriginal := C004.records[1]'(by decide)
theorem original_id513 : original513.index = 513 := by decide

def c513 : Contract := original513.toContract.get (by decide)
theorem binding513 : original513.toContract = some c513 := rfl

theorem checked513 : check 4000 c513 = true := by decide

def original514 : RawOriginal := C004.records[2]'(by decide)
theorem original_id514 : original514.index = 514 := by decide

def c514 : Contract := original514.toContract.get (by decide)
theorem binding514 : original514.toContract = some c514 := rfl

theorem checked514 : check 4000 c514 = true := by decide

def original515 : RawOriginal := C004.records[3]'(by decide)
theorem original_id515 : original515.index = 515 := by decide

def c515 : Contract := original515.toContract.get (by decide)
theorem binding515 : original515.toContract = some c515 := rfl

theorem checked515 : check 4000 c515 = true := by decide

def original516 : RawOriginal := C004.records[4]'(by decide)
theorem original_id516 : original516.index = 516 := by decide

def c516 : Contract := original516.toContract.get (by decide)
theorem binding516 : original516.toContract = some c516 := rfl

theorem checked516 : check 4000 c516 = true := by decide

def original517 : RawOriginal := C004.records[5]'(by decide)
theorem original_id517 : original517.index = 517 := by decide

def c517 : Contract := original517.toContract.get (by decide)
theorem binding517 : original517.toContract = some c517 := rfl

theorem checked517 : check 4000 c517 = true := by decide

def records : List Certified := [
  ⟨502, c502, 4000, checked502⟩,
  ⟨503, c503, 4000, checked503⟩,
  ⟨504, c504, 4000, checked504⟩,
  ⟨505, c505, 4000, checked505⟩,
  ⟨506, c506, 4000, checked506⟩,
  ⟨507, c507, 4000, checked507⟩,
  ⟨508, c508, 4000, checked508⟩,
  ⟨509, c509, 4000, checked509⟩,
  ⟨510, c510, 4000, checked510⟩,
  ⟨511, c511, 4000, checked511⟩,
  ⟨512, c512, 4000, checked512⟩,
  ⟨513, c513, 4000, checked513⟩,
  ⟨514, c514, 4000, checked514⟩,
  ⟨515, c515, 4000, checked515⟩,
  ⟨516, c516, 4000, checked516⟩,
  ⟨517, c517, 4000, checked517⟩]

end PA215.ContractShards.Shard003Part7
