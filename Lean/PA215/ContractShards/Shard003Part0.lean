import PA215.CertifiedContracts
import PA215.Census.C003
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard003Part0
open PA215.Contracts PA215.Census

def original390 : RawOriginal := C003.records[6]'(by decide)
theorem original_id390 : original390.index = 390 := by decide

def c390 : Contract := original390.toContract.get (by decide)
theorem binding390 : original390.toContract = some c390 := rfl

theorem checked390 : check 4000 c390 = true := by decide

def original391 : RawOriginal := C003.records[7]'(by decide)
theorem original_id391 : original391.index = 391 := by decide

def c391 : Contract := original391.toContract.get (by decide)
theorem binding391 : original391.toContract = some c391 := rfl

theorem checked391 : check 4000 c391 = true := by decide

def original392 : RawOriginal := C003.records[8]'(by decide)
theorem original_id392 : original392.index = 392 := by decide

def c392 : Contract := original392.toContract.get (by decide)
theorem binding392 : original392.toContract = some c392 := rfl

theorem checked392 : check 4000 c392 = true := by decide

def original393 : RawOriginal := C003.records[9]'(by decide)
theorem original_id393 : original393.index = 393 := by decide

def c393 : Contract := original393.toContract.get (by decide)
theorem binding393 : original393.toContract = some c393 := rfl

theorem checked393 : check 4000 c393 = true := by decide

def original394 : RawOriginal := C003.records[10]'(by decide)
theorem original_id394 : original394.index = 394 := by decide

def c394 : Contract := original394.toContract.get (by decide)
theorem binding394 : original394.toContract = some c394 := rfl

theorem checked394 : check 4000 c394 = true := by decide

def original395 : RawOriginal := C003.records[11]'(by decide)
theorem original_id395 : original395.index = 395 := by decide

def c395 : Contract := original395.toContract.get (by decide)
theorem binding395 : original395.toContract = some c395 := rfl

theorem checked395 : check 4000 c395 = true := by decide

def original396 : RawOriginal := C003.records[12]'(by decide)
theorem original_id396 : original396.index = 396 := by decide

def c396 : Contract := original396.toContract.get (by decide)
theorem binding396 : original396.toContract = some c396 := rfl

theorem checked396 : check 4000 c396 = true := by decide

def original397 : RawOriginal := C003.records[13]'(by decide)
theorem original_id397 : original397.index = 397 := by decide

def c397 : Contract := original397.toContract.get (by decide)
theorem binding397 : original397.toContract = some c397 := rfl

theorem checked397 : check 4000 c397 = true := by decide

def original398 : RawOriginal := C003.records[14]'(by decide)
theorem original_id398 : original398.index = 398 := by decide

def c398 : Contract := original398.toContract.get (by decide)
theorem binding398 : original398.toContract = some c398 := rfl

theorem checked398 : check 4000 c398 = true := by decide

def original399 : RawOriginal := C003.records[15]'(by decide)
theorem original_id399 : original399.index = 399 := by decide

def c399 : Contract := original399.toContract.get (by decide)
theorem binding399 : original399.toContract = some c399 := rfl

theorem checked399 : check 4000 c399 = true := by decide

def original400 : RawOriginal := C003.records[16]'(by decide)
theorem original_id400 : original400.index = 400 := by decide

def c400 : Contract := original400.toContract.get (by decide)
theorem binding400 : original400.toContract = some c400 := rfl

theorem checked400 : check 4000 c400 = true := by decide

def original401 : RawOriginal := C003.records[17]'(by decide)
theorem original_id401 : original401.index = 401 := by decide

def c401 : Contract := original401.toContract.get (by decide)
theorem binding401 : original401.toContract = some c401 := rfl

theorem checked401 : check 4000 c401 = true := by decide

def original402 : RawOriginal := C003.records[18]'(by decide)
theorem original_id402 : original402.index = 402 := by decide

def c402 : Contract := original402.toContract.get (by decide)
theorem binding402 : original402.toContract = some c402 := rfl

theorem checked402 : check 4000 c402 = true := by decide

def original403 : RawOriginal := C003.records[19]'(by decide)
theorem original_id403 : original403.index = 403 := by decide

def c403 : Contract := original403.toContract.get (by decide)
theorem binding403 : original403.toContract = some c403 := rfl

theorem checked403 : check 4000 c403 = true := by decide

def original404 : RawOriginal := C003.records[20]'(by decide)
theorem original_id404 : original404.index = 404 := by decide

def c404 : Contract := original404.toContract.get (by decide)
theorem binding404 : original404.toContract = some c404 := rfl

theorem checked404 : check 4000 c404 = true := by decide

def original405 : RawOriginal := C003.records[21]'(by decide)
theorem original_id405 : original405.index = 405 := by decide

def c405 : Contract := original405.toContract.get (by decide)
theorem binding405 : original405.toContract = some c405 := rfl

theorem checked405 : check 4000 c405 = true := by decide

def records : List Certified := [
  ⟨390, c390, 4000, checked390⟩,
  ⟨391, c391, 4000, checked391⟩,
  ⟨392, c392, 4000, checked392⟩,
  ⟨393, c393, 4000, checked393⟩,
  ⟨394, c394, 4000, checked394⟩,
  ⟨395, c395, 4000, checked395⟩,
  ⟨396, c396, 4000, checked396⟩,
  ⟨397, c397, 4000, checked397⟩,
  ⟨398, c398, 4000, checked398⟩,
  ⟨399, c399, 4000, checked399⟩,
  ⟨400, c400, 4000, checked400⟩,
  ⟨401, c401, 4000, checked401⟩,
  ⟨402, c402, 4000, checked402⟩,
  ⟨403, c403, 4000, checked403⟩,
  ⟨404, c404, 4000, checked404⟩,
  ⟨405, c405, 4000, checked405⟩]

end PA215.ContractShards.Shard003Part0
