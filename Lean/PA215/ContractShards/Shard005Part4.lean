import PA215.CertifiedContracts
import PA215.Census.C005
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard005Part4
open PA215.Contracts PA215.Census

def original710 : RawOriginal := C005.records[70]'(by decide)
theorem original_id710 : original710.index = 710 := by decide

def c710 : Contract := original710.toContract.get (by decide)
theorem binding710 : original710.toContract = some c710 := rfl

theorem checked710 : check 4000 c710 = true := by decide

def original711 : RawOriginal := C005.records[71]'(by decide)
theorem original_id711 : original711.index = 711 := by decide

def c711 : Contract := original711.toContract.get (by decide)
theorem binding711 : original711.toContract = some c711 := rfl

theorem checked711 : check 4000 c711 = true := by decide

def original712 : RawOriginal := C005.records[72]'(by decide)
theorem original_id712 : original712.index = 712 := by decide

def c712 : Contract := original712.toContract.get (by decide)
theorem binding712 : original712.toContract = some c712 := rfl

theorem checked712 : check 4000 c712 = true := by decide

def original713 : RawOriginal := C005.records[73]'(by decide)
theorem original_id713 : original713.index = 713 := by decide

def c713 : Contract := original713.toContract.get (by decide)
theorem binding713 : original713.toContract = some c713 := rfl

theorem checked713 : check 4000 c713 = true := by decide

def original714 : RawOriginal := C005.records[74]'(by decide)
theorem original_id714 : original714.index = 714 := by decide

def c714 : Contract := original714.toContract.get (by decide)
theorem binding714 : original714.toContract = some c714 := rfl

theorem checked714 : check 4000 c714 = true := by decide

def original715 : RawOriginal := C005.records[75]'(by decide)
theorem original_id715 : original715.index = 715 := by decide

def c715 : Contract := original715.toContract.get (by decide)
theorem binding715 : original715.toContract = some c715 := rfl

theorem checked715 : check 4000 c715 = true := by decide

def original716 : RawOriginal := C005.records[76]'(by decide)
theorem original_id716 : original716.index = 716 := by decide

def c716 : Contract := original716.toContract.get (by decide)
theorem binding716 : original716.toContract = some c716 := rfl

theorem checked716 : check 4000 c716 = true := by decide

def original717 : RawOriginal := C005.records[77]'(by decide)
theorem original_id717 : original717.index = 717 := by decide

def c717 : Contract := original717.toContract.get (by decide)
theorem binding717 : original717.toContract = some c717 := rfl

theorem checked717 : check 4000 c717 = true := by decide

def original718 : RawOriginal := C005.records[78]'(by decide)
theorem original_id718 : original718.index = 718 := by decide

def c718 : Contract := original718.toContract.get (by decide)
theorem binding718 : original718.toContract = some c718 := rfl

theorem checked718 : check 4000 c718 = true := by decide

def original719 : RawOriginal := C005.records[79]'(by decide)
theorem original_id719 : original719.index = 719 := by decide

def c719 : Contract := original719.toContract.get (by decide)
theorem binding719 : original719.toContract = some c719 := rfl

theorem checked719 : check 4000 c719 = true := by decide

def original720 : RawOriginal := C005.records[80]'(by decide)
theorem original_id720 : original720.index = 720 := by decide

def c720 : Contract := original720.toContract.get (by decide)
theorem binding720 : original720.toContract = some c720 := rfl

theorem checked720 : check 4000 c720 = true := by decide

def original721 : RawOriginal := C005.records[81]'(by decide)
theorem original_id721 : original721.index = 721 := by decide

def c721 : Contract := original721.toContract.get (by decide)
theorem binding721 : original721.toContract = some c721 := rfl

theorem checked721 : check 4000 c721 = true := by decide

def original722 : RawOriginal := C005.records[82]'(by decide)
theorem original_id722 : original722.index = 722 := by decide

def c722 : Contract := original722.toContract.get (by decide)
theorem binding722 : original722.toContract = some c722 := rfl

theorem checked722 : check 4000 c722 = true := by decide

def original723 : RawOriginal := C005.records[83]'(by decide)
theorem original_id723 : original723.index = 723 := by decide

def c723 : Contract := original723.toContract.get (by decide)
theorem binding723 : original723.toContract = some c723 := rfl

theorem checked723 : check 4000 c723 = true := by decide

def original724 : RawOriginal := C005.records[84]'(by decide)
theorem original_id724 : original724.index = 724 := by decide

def c724 : Contract := original724.toContract.get (by decide)
theorem binding724 : original724.toContract = some c724 := rfl

theorem checked724 : check 4000 c724 = true := by decide

def original725 : RawOriginal := C005.records[85]'(by decide)
theorem original_id725 : original725.index = 725 := by decide

def c725 : Contract := original725.toContract.get (by decide)
theorem binding725 : original725.toContract = some c725 := rfl

theorem checked725 : check 4000 c725 = true := by decide

def records : List Certified := [
  ⟨710, c710, 4000, checked710⟩,
  ⟨711, c711, 4000, checked711⟩,
  ⟨712, c712, 4000, checked712⟩,
  ⟨713, c713, 4000, checked713⟩,
  ⟨714, c714, 4000, checked714⟩,
  ⟨715, c715, 4000, checked715⟩,
  ⟨716, c716, 4000, checked716⟩,
  ⟨717, c717, 4000, checked717⟩,
  ⟨718, c718, 4000, checked718⟩,
  ⟨719, c719, 4000, checked719⟩,
  ⟨720, c720, 4000, checked720⟩,
  ⟨721, c721, 4000, checked721⟩,
  ⟨722, c722, 4000, checked722⟩,
  ⟨723, c723, 4000, checked723⟩,
  ⟨724, c724, 4000, checked724⟩,
  ⟨725, c725, 4000, checked725⟩]

end PA215.ContractShards.Shard005Part4
