import PA215.CertifiedContracts
import PA215.Census.C007
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard007Part6
open PA215.Contracts PA215.Census

def original998 : RawOriginal := C007.records[102]'(by decide)
theorem original_id998 : original998.index = 998 := by decide

def c998 : Contract := original998.toContract.get (by decide)
theorem binding998 : original998.toContract = some c998 := rfl

theorem checked998 : check 4000 c998 = true := by decide

def original999 : RawOriginal := C007.records[103]'(by decide)
theorem original_id999 : original999.index = 999 := by decide

def c999 : Contract := original999.toContract.get (by decide)
theorem binding999 : original999.toContract = some c999 := rfl

theorem checked999 : check 4000 c999 = true := by decide

def original1000 : RawOriginal := C007.records[104]'(by decide)
theorem original_id1000 : original1000.index = 1000 := by decide

def c1000 : Contract := original1000.toContract.get (by decide)
theorem binding1000 : original1000.toContract = some c1000 := rfl

theorem checked1000 : check 4000 c1000 = true := by decide

def original1001 : RawOriginal := C007.records[105]'(by decide)
theorem original_id1001 : original1001.index = 1001 := by decide

def c1001 : Contract := original1001.toContract.get (by decide)
theorem binding1001 : original1001.toContract = some c1001 := rfl

theorem checked1001 : check 4000 c1001 = true := by decide

def original1002 : RawOriginal := C007.records[106]'(by decide)
theorem original_id1002 : original1002.index = 1002 := by decide

def c1002 : Contract := original1002.toContract.get (by decide)
theorem binding1002 : original1002.toContract = some c1002 := rfl

theorem checked1002 : check 4000 c1002 = true := by decide

def original1003 : RawOriginal := C007.records[107]'(by decide)
theorem original_id1003 : original1003.index = 1003 := by decide

def c1003 : Contract := original1003.toContract.get (by decide)
theorem binding1003 : original1003.toContract = some c1003 := rfl

theorem checked1003 : check 4000 c1003 = true := by decide

def original1004 : RawOriginal := C007.records[108]'(by decide)
theorem original_id1004 : original1004.index = 1004 := by decide

def c1004 : Contract := original1004.toContract.get (by decide)
theorem binding1004 : original1004.toContract = some c1004 := rfl

theorem checked1004 : check 4000 c1004 = true := by decide

def original1005 : RawOriginal := C007.records[109]'(by decide)
theorem original_id1005 : original1005.index = 1005 := by decide

def c1005 : Contract := original1005.toContract.get (by decide)
theorem binding1005 : original1005.toContract = some c1005 := rfl

theorem checked1005 : check 4000 c1005 = true := by decide

def original1006 : RawOriginal := C007.records[110]'(by decide)
theorem original_id1006 : original1006.index = 1006 := by decide

def c1006 : Contract := original1006.toContract.get (by decide)
theorem binding1006 : original1006.toContract = some c1006 := rfl

theorem checked1006 : check 4000 c1006 = true := by decide

def original1007 : RawOriginal := C007.records[111]'(by decide)
theorem original_id1007 : original1007.index = 1007 := by decide

def c1007 : Contract := original1007.toContract.get (by decide)
theorem binding1007 : original1007.toContract = some c1007 := rfl

theorem checked1007 : check 4000 c1007 = true := by decide

def original1008 : RawOriginal := C007.records[112]'(by decide)
theorem original_id1008 : original1008.index = 1008 := by decide

def c1008 : Contract := original1008.toContract.get (by decide)
theorem binding1008 : original1008.toContract = some c1008 := rfl

theorem checked1008 : check 4000 c1008 = true := by decide

def original1009 : RawOriginal := C007.records[113]'(by decide)
theorem original_id1009 : original1009.index = 1009 := by decide

def c1009 : Contract := original1009.toContract.get (by decide)
theorem binding1009 : original1009.toContract = some c1009 := rfl

theorem checked1009 : check 4000 c1009 = true := by decide

def original1010 : RawOriginal := C007.records[114]'(by decide)
theorem original_id1010 : original1010.index = 1010 := by decide

def c1010 : Contract := original1010.toContract.get (by decide)
theorem binding1010 : original1010.toContract = some c1010 := rfl

theorem checked1010 : check 4000 c1010 = true := by decide

def original1011 : RawOriginal := C007.records[115]'(by decide)
theorem original_id1011 : original1011.index = 1011 := by decide

def c1011 : Contract := original1011.toContract.get (by decide)
theorem binding1011 : original1011.toContract = some c1011 := rfl

theorem checked1011 : check 4000 c1011 = true := by decide

def original1012 : RawOriginal := C007.records[116]'(by decide)
theorem original_id1012 : original1012.index = 1012 := by decide

def c1012 : Contract := original1012.toContract.get (by decide)
theorem binding1012 : original1012.toContract = some c1012 := rfl

theorem checked1012 : check 4000 c1012 = true := by decide

def original1013 : RawOriginal := C007.records[117]'(by decide)
theorem original_id1013 : original1013.index = 1013 := by decide

def c1013 : Contract := original1013.toContract.get (by decide)
theorem binding1013 : original1013.toContract = some c1013 := rfl

theorem checked1013 : check 4000 c1013 = true := by decide

def records : List Certified := [
  ⟨998, c998, 4000, checked998⟩,
  ⟨999, c999, 4000, checked999⟩,
  ⟨1000, c1000, 4000, checked1000⟩,
  ⟨1001, c1001, 4000, checked1001⟩,
  ⟨1002, c1002, 4000, checked1002⟩,
  ⟨1003, c1003, 4000, checked1003⟩,
  ⟨1004, c1004, 4000, checked1004⟩,
  ⟨1005, c1005, 4000, checked1005⟩,
  ⟨1006, c1006, 4000, checked1006⟩,
  ⟨1007, c1007, 4000, checked1007⟩,
  ⟨1008, c1008, 4000, checked1008⟩,
  ⟨1009, c1009, 4000, checked1009⟩,
  ⟨1010, c1010, 4000, checked1010⟩,
  ⟨1011, c1011, 4000, checked1011⟩,
  ⟨1012, c1012, 4000, checked1012⟩,
  ⟨1013, c1013, 4000, checked1013⟩]

end PA215.ContractShards.Shard007Part6
