import PA215.CertifiedContracts
import PA215.Census.C004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard004Part0
open PA215.Contracts PA215.Census

def original518 : RawOriginal := C004.records[6]'(by decide)
theorem original_id518 : original518.index = 518 := by decide

def c518 : Contract := original518.toContract.get (by decide)
theorem binding518 : original518.toContract = some c518 := rfl

theorem checked518 : check 4000 c518 = true := by decide

def original519 : RawOriginal := C004.records[7]'(by decide)
theorem original_id519 : original519.index = 519 := by decide

def c519 : Contract := original519.toContract.get (by decide)
theorem binding519 : original519.toContract = some c519 := rfl

theorem checked519 : check 4000 c519 = true := by decide

def original520 : RawOriginal := C004.records[8]'(by decide)
theorem original_id520 : original520.index = 520 := by decide

def c520 : Contract := original520.toContract.get (by decide)
theorem binding520 : original520.toContract = some c520 := rfl

theorem checked520 : check 4000 c520 = true := by decide

def original521 : RawOriginal := C004.records[9]'(by decide)
theorem original_id521 : original521.index = 521 := by decide

def c521 : Contract := original521.toContract.get (by decide)
theorem binding521 : original521.toContract = some c521 := rfl

theorem checked521 : check 4000 c521 = true := by decide

def original522 : RawOriginal := C004.records[10]'(by decide)
theorem original_id522 : original522.index = 522 := by decide

def c522 : Contract := original522.toContract.get (by decide)
theorem binding522 : original522.toContract = some c522 := rfl

theorem checked522 : check 4000 c522 = true := by decide

def original523 : RawOriginal := C004.records[11]'(by decide)
theorem original_id523 : original523.index = 523 := by decide

def c523 : Contract := original523.toContract.get (by decide)
theorem binding523 : original523.toContract = some c523 := rfl

theorem checked523 : check 4000 c523 = true := by decide

def original524 : RawOriginal := C004.records[12]'(by decide)
theorem original_id524 : original524.index = 524 := by decide

def c524 : Contract := original524.toContract.get (by decide)
theorem binding524 : original524.toContract = some c524 := rfl

theorem checked524 : check 4000 c524 = true := by decide

def original525 : RawOriginal := C004.records[13]'(by decide)
theorem original_id525 : original525.index = 525 := by decide

def c525 : Contract := original525.toContract.get (by decide)
theorem binding525 : original525.toContract = some c525 := rfl

theorem checked525 : check 4000 c525 = true := by decide

def original526 : RawOriginal := C004.records[14]'(by decide)
theorem original_id526 : original526.index = 526 := by decide

def c526 : Contract := original526.toContract.get (by decide)
theorem binding526 : original526.toContract = some c526 := rfl

theorem checked526 : check 4000 c526 = true := by decide

def original527 : RawOriginal := C004.records[15]'(by decide)
theorem original_id527 : original527.index = 527 := by decide

def c527 : Contract := original527.toContract.get (by decide)
theorem binding527 : original527.toContract = some c527 := rfl

theorem checked527 : check 4000 c527 = true := by decide

def original528 : RawOriginal := C004.records[16]'(by decide)
theorem original_id528 : original528.index = 528 := by decide

def c528 : Contract := original528.toContract.get (by decide)
theorem binding528 : original528.toContract = some c528 := rfl

theorem checked528 : check 4000 c528 = true := by decide

def original529 : RawOriginal := C004.records[17]'(by decide)
theorem original_id529 : original529.index = 529 := by decide

def c529 : Contract := original529.toContract.get (by decide)
theorem binding529 : original529.toContract = some c529 := rfl

theorem checked529 : check 4000 c529 = true := by decide

def original530 : RawOriginal := C004.records[18]'(by decide)
theorem original_id530 : original530.index = 530 := by decide

def c530 : Contract := original530.toContract.get (by decide)
theorem binding530 : original530.toContract = some c530 := rfl

theorem checked530 : check 4000 c530 = true := by decide

def original531 : RawOriginal := C004.records[19]'(by decide)
theorem original_id531 : original531.index = 531 := by decide

def c531 : Contract := original531.toContract.get (by decide)
theorem binding531 : original531.toContract = some c531 := rfl

theorem checked531 : check 4000 c531 = true := by decide

def original532 : RawOriginal := C004.records[20]'(by decide)
theorem original_id532 : original532.index = 532 := by decide

def c532 : Contract := original532.toContract.get (by decide)
theorem binding532 : original532.toContract = some c532 := rfl

theorem checked532 : check 4000 c532 = true := by decide

def original533 : RawOriginal := C004.records[21]'(by decide)
theorem original_id533 : original533.index = 533 := by decide

def c533 : Contract := original533.toContract.get (by decide)
theorem binding533 : original533.toContract = some c533 := rfl

theorem checked533 : check 4000 c533 = true := by decide

def records : List Certified := [
  ⟨518, c518, 4000, checked518⟩,
  ⟨519, c519, 4000, checked519⟩,
  ⟨520, c520, 4000, checked520⟩,
  ⟨521, c521, 4000, checked521⟩,
  ⟨522, c522, 4000, checked522⟩,
  ⟨523, c523, 4000, checked523⟩,
  ⟨524, c524, 4000, checked524⟩,
  ⟨525, c525, 4000, checked525⟩,
  ⟨526, c526, 4000, checked526⟩,
  ⟨527, c527, 4000, checked527⟩,
  ⟨528, c528, 4000, checked528⟩,
  ⟨529, c529, 4000, checked529⟩,
  ⟨530, c530, 4000, checked530⟩,
  ⟨531, c531, 4000, checked531⟩,
  ⟨532, c532, 4000, checked532⟩,
  ⟨533, c533, 4000, checked533⟩]

end PA215.ContractShards.Shard004Part0
