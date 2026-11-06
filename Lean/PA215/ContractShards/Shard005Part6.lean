import PA215.CertifiedContracts
import PA215.Census.C005
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard005Part6
open PA215.Contracts PA215.Census

def original742 : RawOriginal := C005.records[102]'(by decide)
theorem original_id742 : original742.index = 742 := by decide

def c742 : Contract := original742.toContract.get (by decide)
theorem binding742 : original742.toContract = some c742 := rfl

theorem checked742 : check 4000 c742 = true := by decide

def original743 : RawOriginal := C005.records[103]'(by decide)
theorem original_id743 : original743.index = 743 := by decide

def c743 : Contract := original743.toContract.get (by decide)
theorem binding743 : original743.toContract = some c743 := rfl

theorem checked743 : check 4000 c743 = true := by decide

def original744 : RawOriginal := C005.records[104]'(by decide)
theorem original_id744 : original744.index = 744 := by decide

def c744 : Contract := original744.toContract.get (by decide)
theorem binding744 : original744.toContract = some c744 := rfl

theorem checked744 : check 4000 c744 = true := by decide

def original745 : RawOriginal := C005.records[105]'(by decide)
theorem original_id745 : original745.index = 745 := by decide

def c745 : Contract := original745.toContract.get (by decide)
theorem binding745 : original745.toContract = some c745 := rfl

theorem checked745 : check 4000 c745 = true := by decide

def original746 : RawOriginal := C005.records[106]'(by decide)
theorem original_id746 : original746.index = 746 := by decide

def c746 : Contract := original746.toContract.get (by decide)
theorem binding746 : original746.toContract = some c746 := rfl

theorem checked746 : check 4000 c746 = true := by decide

def original747 : RawOriginal := C005.records[107]'(by decide)
theorem original_id747 : original747.index = 747 := by decide

def c747 : Contract := original747.toContract.get (by decide)
theorem binding747 : original747.toContract = some c747 := rfl

theorem checked747 : check 4000 c747 = true := by decide

def original748 : RawOriginal := C005.records[108]'(by decide)
theorem original_id748 : original748.index = 748 := by decide

def c748 : Contract := original748.toContract.get (by decide)
theorem binding748 : original748.toContract = some c748 := rfl

theorem checked748 : check 4000 c748 = true := by decide

def original749 : RawOriginal := C005.records[109]'(by decide)
theorem original_id749 : original749.index = 749 := by decide

def c749 : Contract := original749.toContract.get (by decide)
theorem binding749 : original749.toContract = some c749 := rfl

theorem checked749 : check 4000 c749 = true := by decide

def original750 : RawOriginal := C005.records[110]'(by decide)
theorem original_id750 : original750.index = 750 := by decide

def c750 : Contract := original750.toContract.get (by decide)
theorem binding750 : original750.toContract = some c750 := rfl

theorem checked750 : check 4000 c750 = true := by decide

def original751 : RawOriginal := C005.records[111]'(by decide)
theorem original_id751 : original751.index = 751 := by decide

def c751 : Contract := original751.toContract.get (by decide)
theorem binding751 : original751.toContract = some c751 := rfl

theorem checked751 : check 4000 c751 = true := by decide

def original752 : RawOriginal := C005.records[112]'(by decide)
theorem original_id752 : original752.index = 752 := by decide

def c752 : Contract := original752.toContract.get (by decide)
theorem binding752 : original752.toContract = some c752 := rfl

theorem checked752 : check 4000 c752 = true := by decide

def original753 : RawOriginal := C005.records[113]'(by decide)
theorem original_id753 : original753.index = 753 := by decide

def c753 : Contract := original753.toContract.get (by decide)
theorem binding753 : original753.toContract = some c753 := rfl

theorem checked753 : check 4000 c753 = true := by decide

def original754 : RawOriginal := C005.records[114]'(by decide)
theorem original_id754 : original754.index = 754 := by decide

def c754 : Contract := original754.toContract.get (by decide)
theorem binding754 : original754.toContract = some c754 := rfl

theorem checked754 : check 4000 c754 = true := by decide

def original755 : RawOriginal := C005.records[115]'(by decide)
theorem original_id755 : original755.index = 755 := by decide

def c755 : Contract := original755.toContract.get (by decide)
theorem binding755 : original755.toContract = some c755 := rfl

theorem checked755 : check 4000 c755 = true := by decide

def original756 : RawOriginal := C005.records[116]'(by decide)
theorem original_id756 : original756.index = 756 := by decide

def c756 : Contract := original756.toContract.get (by decide)
theorem binding756 : original756.toContract = some c756 := rfl

theorem checked756 : check 4000 c756 = true := by decide

def original757 : RawOriginal := C005.records[117]'(by decide)
theorem original_id757 : original757.index = 757 := by decide

def c757 : Contract := original757.toContract.get (by decide)
theorem binding757 : original757.toContract = some c757 := rfl

theorem checked757 : check 4000 c757 = true := by decide

def records : List Certified := [
  ⟨742, c742, 4000, checked742⟩,
  ⟨743, c743, 4000, checked743⟩,
  ⟨744, c744, 4000, checked744⟩,
  ⟨745, c745, 4000, checked745⟩,
  ⟨746, c746, 4000, checked746⟩,
  ⟨747, c747, 4000, checked747⟩,
  ⟨748, c748, 4000, checked748⟩,
  ⟨749, c749, 4000, checked749⟩,
  ⟨750, c750, 4000, checked750⟩,
  ⟨751, c751, 4000, checked751⟩,
  ⟨752, c752, 4000, checked752⟩,
  ⟨753, c753, 4000, checked753⟩,
  ⟨754, c754, 4000, checked754⟩,
  ⟨755, c755, 4000, checked755⟩,
  ⟨756, c756, 4000, checked756⟩,
  ⟨757, c757, 4000, checked757⟩]

end PA215.ContractShards.Shard005Part6
