import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C023
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard023Part3
open PA215.Contracts PA215.Census

def original2998 : RawOriginal := C023.records[54]'(by decide)
theorem original_id2998 : original2998.index = 2998 := by decide

def c2998 : Contract := original2998.toContract.get (by decide)
theorem binding2998 : original2998.toContract = some c2998 := rfl

theorem checked2998 : check 4000 c2998 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2999 : RawOriginal := C023.records[55]'(by decide)
theorem original_id2999 : original2999.index = 2999 := by decide

def c2999 : Contract := original2999.toContract.get (by decide)
theorem binding2999 : original2999.toContract = some c2999 := rfl

theorem checked2999 : check 4000 c2999 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3000 : RawOriginal := C023.records[56]'(by decide)
theorem original_id3000 : original3000.index = 3000 := by decide

def c3000 : Contract := original3000.toContract.get (by decide)
theorem binding3000 : original3000.toContract = some c3000 := rfl

theorem checked3000 : check 4000 c3000 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3001 : RawOriginal := C023.records[57]'(by decide)
theorem original_id3001 : original3001.index = 3001 := by decide

def c3001 : Contract := original3001.toContract.get (by decide)
theorem binding3001 : original3001.toContract = some c3001 := rfl

theorem checked3001 : check 4000 c3001 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3002 : RawOriginal := C023.records[58]'(by decide)
theorem original_id3002 : original3002.index = 3002 := by decide

def c3002 : Contract := original3002.toContract.get (by decide)
theorem binding3002 : original3002.toContract = some c3002 := rfl

theorem checked3002 : check 4000 c3002 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3003 : RawOriginal := C023.records[59]'(by decide)
theorem original_id3003 : original3003.index = 3003 := by decide

def c3003 : Contract := original3003.toContract.get (by decide)
theorem binding3003 : original3003.toContract = some c3003 := rfl

theorem checked3003 : check 4000 c3003 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3004 : RawOriginal := C023.records[60]'(by decide)
theorem original_id3004 : original3004.index = 3004 := by decide

def c3004 : Contract := original3004.toContract.get (by decide)
theorem binding3004 : original3004.toContract = some c3004 := rfl

theorem checked3004 : check 4000 c3004 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3005 : RawOriginal := C023.records[61]'(by decide)
theorem original_id3005 : original3005.index = 3005 := by decide

def c3005 : Contract := original3005.toContract.get (by decide)
theorem binding3005 : original3005.toContract = some c3005 := rfl

theorem checked3005 : check 4000 c3005 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3006 : RawOriginal := C023.records[62]'(by decide)
theorem original_id3006 : original3006.index = 3006 := by decide

def c3006 : Contract := original3006.toContract.get (by decide)
theorem binding3006 : original3006.toContract = some c3006 := rfl

theorem checked3006 : check 4000 c3006 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3007 : RawOriginal := C023.records[63]'(by decide)
theorem original_id3007 : original3007.index = 3007 := by decide

def c3007 : Contract := original3007.toContract.get (by decide)
theorem binding3007 : original3007.toContract = some c3007 := rfl

theorem checked3007 : check 4000 c3007 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3008 : RawOriginal := C023.records[64]'(by decide)
theorem original_id3008 : original3008.index = 3008 := by decide

def c3008 : Contract := original3008.toContract.get (by decide)
theorem binding3008 : original3008.toContract = some c3008 := rfl

theorem checked3008 : check 4000 c3008 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3009 : RawOriginal := C023.records[65]'(by decide)
theorem original_id3009 : original3009.index = 3009 := by decide

def c3009 : Contract := original3009.toContract.get (by decide)
theorem binding3009 : original3009.toContract = some c3009 := rfl

theorem checked3009 : check 4000 c3009 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3010 : RawOriginal := C023.records[66]'(by decide)
theorem original_id3010 : original3010.index = 3010 := by decide

def c3010 : Contract := original3010.toContract.get (by decide)
theorem binding3010 : original3010.toContract = some c3010 := rfl

theorem checked3010 : check 4000 c3010 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3011 : RawOriginal := C023.records[67]'(by decide)
theorem original_id3011 : original3011.index = 3011 := by decide

def c3011 : Contract := original3011.toContract.get (by decide)
theorem binding3011 : original3011.toContract = some c3011 := rfl

theorem checked3011 : check 4000 c3011 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3012 : RawOriginal := C023.records[68]'(by decide)
theorem original_id3012 : original3012.index = 3012 := by decide

def c3012 : Contract := original3012.toContract.get (by decide)
theorem binding3012 : original3012.toContract = some c3012 := rfl

theorem checked3012 : check 4000 c3012 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3013 : RawOriginal := C023.records[69]'(by decide)
theorem original_id3013 : original3013.index = 3013 := by decide

def c3013 : Contract := original3013.toContract.get (by decide)
theorem binding3013 : original3013.toContract = some c3013 := rfl

theorem checked3013 : check 4000 c3013 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2998, c2998, 4000, checked2998⟩,
  ⟨2999, c2999, 4000, checked2999⟩,
  ⟨3000, c3000, 4000, checked3000⟩,
  ⟨3001, c3001, 4000, checked3001⟩,
  ⟨3002, c3002, 4000, checked3002⟩,
  ⟨3003, c3003, 4000, checked3003⟩,
  ⟨3004, c3004, 4000, checked3004⟩,
  ⟨3005, c3005, 4000, checked3005⟩,
  ⟨3006, c3006, 4000, checked3006⟩,
  ⟨3007, c3007, 4000, checked3007⟩,
  ⟨3008, c3008, 4000, checked3008⟩,
  ⟨3009, c3009, 4000, checked3009⟩,
  ⟨3010, c3010, 4000, checked3010⟩,
  ⟨3011, c3011, 4000, checked3011⟩,
  ⟨3012, c3012, 4000, checked3012⟩,
  ⟨3013, c3013, 4000, checked3013⟩]

end PA215.ContractShards.Shard023Part3
