import PA215.CertifiedContracts
import PA215.Census.C003
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard003Part4
open PA215.Contracts PA215.Census

def original454 : RawOriginal := C003.records[70]'(by decide)
theorem original_id454 : original454.index = 454 := by decide

def c454 : Contract := original454.toContract.get (by decide)
theorem binding454 : original454.toContract = some c454 := rfl

theorem checked454 : check 4000 c454 = true := by decide

def original455 : RawOriginal := C003.records[71]'(by decide)
theorem original_id455 : original455.index = 455 := by decide

def c455 : Contract := original455.toContract.get (by decide)
theorem binding455 : original455.toContract = some c455 := rfl

theorem checked455 : check 4000 c455 = true := by decide

def original456 : RawOriginal := C003.records[72]'(by decide)
theorem original_id456 : original456.index = 456 := by decide

def c456 : Contract := original456.toContract.get (by decide)
theorem binding456 : original456.toContract = some c456 := rfl

theorem checked456 : check 4000 c456 = true := by decide

def original457 : RawOriginal := C003.records[73]'(by decide)
theorem original_id457 : original457.index = 457 := by decide

def c457 : Contract := original457.toContract.get (by decide)
theorem binding457 : original457.toContract = some c457 := rfl

theorem checked457 : check 4000 c457 = true := by decide

def original458 : RawOriginal := C003.records[74]'(by decide)
theorem original_id458 : original458.index = 458 := by decide

def c458 : Contract := original458.toContract.get (by decide)
theorem binding458 : original458.toContract = some c458 := rfl

theorem checked458 : check 4000 c458 = true := by decide

def original459 : RawOriginal := C003.records[75]'(by decide)
theorem original_id459 : original459.index = 459 := by decide

def c459 : Contract := original459.toContract.get (by decide)
theorem binding459 : original459.toContract = some c459 := rfl

theorem checked459 : check 4000 c459 = true := by decide

def original460 : RawOriginal := C003.records[76]'(by decide)
theorem original_id460 : original460.index = 460 := by decide

def c460 : Contract := original460.toContract.get (by decide)
theorem binding460 : original460.toContract = some c460 := rfl

theorem checked460 : check 4000 c460 = true := by decide

def original461 : RawOriginal := C003.records[77]'(by decide)
theorem original_id461 : original461.index = 461 := by decide

def c461 : Contract := original461.toContract.get (by decide)
theorem binding461 : original461.toContract = some c461 := rfl

theorem checked461 : check 4000 c461 = true := by decide

def original462 : RawOriginal := C003.records[78]'(by decide)
theorem original_id462 : original462.index = 462 := by decide

def c462 : Contract := original462.toContract.get (by decide)
theorem binding462 : original462.toContract = some c462 := rfl

theorem checked462 : check 4000 c462 = true := by decide

def original463 : RawOriginal := C003.records[79]'(by decide)
theorem original_id463 : original463.index = 463 := by decide

def c463 : Contract := original463.toContract.get (by decide)
theorem binding463 : original463.toContract = some c463 := rfl

theorem checked463 : check 4000 c463 = true := by decide

def original464 : RawOriginal := C003.records[80]'(by decide)
theorem original_id464 : original464.index = 464 := by decide

def c464 : Contract := original464.toContract.get (by decide)
theorem binding464 : original464.toContract = some c464 := rfl

theorem checked464 : check 4000 c464 = true := by decide

def original465 : RawOriginal := C003.records[81]'(by decide)
theorem original_id465 : original465.index = 465 := by decide

def c465 : Contract := original465.toContract.get (by decide)
theorem binding465 : original465.toContract = some c465 := rfl

theorem checked465 : check 4000 c465 = true := by decide

def original466 : RawOriginal := C003.records[82]'(by decide)
theorem original_id466 : original466.index = 466 := by decide

def c466 : Contract := original466.toContract.get (by decide)
theorem binding466 : original466.toContract = some c466 := rfl

theorem checked466 : check 4000 c466 = true := by decide

def original467 : RawOriginal := C003.records[83]'(by decide)
theorem original_id467 : original467.index = 467 := by decide

def c467 : Contract := original467.toContract.get (by decide)
theorem binding467 : original467.toContract = some c467 := rfl

theorem checked467 : check 4000 c467 = true := by decide

def original468 : RawOriginal := C003.records[84]'(by decide)
theorem original_id468 : original468.index = 468 := by decide

def c468 : Contract := original468.toContract.get (by decide)
theorem binding468 : original468.toContract = some c468 := rfl

theorem checked468 : check 4000 c468 = true := by decide

def original469 : RawOriginal := C003.records[85]'(by decide)
theorem original_id469 : original469.index = 469 := by decide

def c469 : Contract := original469.toContract.get (by decide)
theorem binding469 : original469.toContract = some c469 := rfl

theorem checked469 : check 4000 c469 = true := by decide

def records : List Certified := [
  ⟨454, c454, 4000, checked454⟩,
  ⟨455, c455, 4000, checked455⟩,
  ⟨456, c456, 4000, checked456⟩,
  ⟨457, c457, 4000, checked457⟩,
  ⟨458, c458, 4000, checked458⟩,
  ⟨459, c459, 4000, checked459⟩,
  ⟨460, c460, 4000, checked460⟩,
  ⟨461, c461, 4000, checked461⟩,
  ⟨462, c462, 4000, checked462⟩,
  ⟨463, c463, 4000, checked463⟩,
  ⟨464, c464, 4000, checked464⟩,
  ⟨465, c465, 4000, checked465⟩,
  ⟨466, c466, 4000, checked466⟩,
  ⟨467, c467, 4000, checked467⟩,
  ⟨468, c468, 4000, checked468⟩,
  ⟨469, c469, 4000, checked469⟩]

end PA215.ContractShards.Shard003Part4
