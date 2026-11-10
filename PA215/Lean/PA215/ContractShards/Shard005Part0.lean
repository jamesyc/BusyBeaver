import PA215.CertifiedContracts
import PA215.Census.C005
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard005Part0
open PA215.Contracts PA215.Census

def original646 : RawOriginal := C005.records[6]'(by decide)
theorem original_id646 : original646.index = 646 := by decide

def c646 : Contract := original646.toContract.get (by decide)
theorem binding646 : original646.toContract = some c646 := rfl

theorem checked646 : check 4000 c646 = true := by decide

def original647 : RawOriginal := C005.records[7]'(by decide)
theorem original_id647 : original647.index = 647 := by decide

def c647 : Contract := original647.toContract.get (by decide)
theorem binding647 : original647.toContract = some c647 := rfl

theorem checked647 : check 4000 c647 = true := by decide

def original648 : RawOriginal := C005.records[8]'(by decide)
theorem original_id648 : original648.index = 648 := by decide

def c648 : Contract := original648.toContract.get (by decide)
theorem binding648 : original648.toContract = some c648 := rfl

theorem checked648 : check 4000 c648 = true := by decide

def original649 : RawOriginal := C005.records[9]'(by decide)
theorem original_id649 : original649.index = 649 := by decide

def c649 : Contract := original649.toContract.get (by decide)
theorem binding649 : original649.toContract = some c649 := rfl

theorem checked649 : check 4000 c649 = true := by decide

def original650 : RawOriginal := C005.records[10]'(by decide)
theorem original_id650 : original650.index = 650 := by decide

def c650 : Contract := original650.toContract.get (by decide)
theorem binding650 : original650.toContract = some c650 := rfl

theorem checked650 : check 4000 c650 = true := by decide

def original651 : RawOriginal := C005.records[11]'(by decide)
theorem original_id651 : original651.index = 651 := by decide

def c651 : Contract := original651.toContract.get (by decide)
theorem binding651 : original651.toContract = some c651 := rfl

theorem checked651 : check 4000 c651 = true := by decide

def original652 : RawOriginal := C005.records[12]'(by decide)
theorem original_id652 : original652.index = 652 := by decide

def c652 : Contract := original652.toContract.get (by decide)
theorem binding652 : original652.toContract = some c652 := rfl

theorem checked652 : check 4000 c652 = true := by decide

def original653 : RawOriginal := C005.records[13]'(by decide)
theorem original_id653 : original653.index = 653 := by decide

def c653 : Contract := original653.toContract.get (by decide)
theorem binding653 : original653.toContract = some c653 := rfl

theorem checked653 : check 4000 c653 = true := by decide

def original654 : RawOriginal := C005.records[14]'(by decide)
theorem original_id654 : original654.index = 654 := by decide

def c654 : Contract := original654.toContract.get (by decide)
theorem binding654 : original654.toContract = some c654 := rfl

theorem checked654 : check 4000 c654 = true := by decide

def original655 : RawOriginal := C005.records[15]'(by decide)
theorem original_id655 : original655.index = 655 := by decide

def c655 : Contract := original655.toContract.get (by decide)
theorem binding655 : original655.toContract = some c655 := rfl

theorem checked655 : check 4000 c655 = true := by decide

def original656 : RawOriginal := C005.records[16]'(by decide)
theorem original_id656 : original656.index = 656 := by decide

def c656 : Contract := original656.toContract.get (by decide)
theorem binding656 : original656.toContract = some c656 := rfl

theorem checked656 : check 4000 c656 = true := by decide

def original657 : RawOriginal := C005.records[17]'(by decide)
theorem original_id657 : original657.index = 657 := by decide

def c657 : Contract := original657.toContract.get (by decide)
theorem binding657 : original657.toContract = some c657 := rfl

theorem checked657 : check 4000 c657 = true := by decide

def original658 : RawOriginal := C005.records[18]'(by decide)
theorem original_id658 : original658.index = 658 := by decide

def c658 : Contract := original658.toContract.get (by decide)
theorem binding658 : original658.toContract = some c658 := rfl

theorem checked658 : check 4000 c658 = true := by decide

def original659 : RawOriginal := C005.records[19]'(by decide)
theorem original_id659 : original659.index = 659 := by decide

def c659 : Contract := original659.toContract.get (by decide)
theorem binding659 : original659.toContract = some c659 := rfl

theorem checked659 : check 4000 c659 = true := by decide

def original660 : RawOriginal := C005.records[20]'(by decide)
theorem original_id660 : original660.index = 660 := by decide

def c660 : Contract := original660.toContract.get (by decide)
theorem binding660 : original660.toContract = some c660 := rfl

theorem checked660 : check 4000 c660 = true := by decide

def original661 : RawOriginal := C005.records[21]'(by decide)
theorem original_id661 : original661.index = 661 := by decide

def c661 : Contract := original661.toContract.get (by decide)
theorem binding661 : original661.toContract = some c661 := rfl

theorem checked661 : check 4000 c661 = true := by decide

def records : List Certified := [
  ⟨646, c646, 4000, checked646⟩,
  ⟨647, c647, 4000, checked647⟩,
  ⟨648, c648, 4000, checked648⟩,
  ⟨649, c649, 4000, checked649⟩,
  ⟨650, c650, 4000, checked650⟩,
  ⟨651, c651, 4000, checked651⟩,
  ⟨652, c652, 4000, checked652⟩,
  ⟨653, c653, 4000, checked653⟩,
  ⟨654, c654, 4000, checked654⟩,
  ⟨655, c655, 4000, checked655⟩,
  ⟨656, c656, 4000, checked656⟩,
  ⟨657, c657, 4000, checked657⟩,
  ⟨658, c658, 4000, checked658⟩,
  ⟨659, c659, 4000, checked659⟩,
  ⟨660, c660, 4000, checked660⟩,
  ⟨661, c661, 4000, checked661⟩]

end PA215.ContractShards.Shard005Part0
