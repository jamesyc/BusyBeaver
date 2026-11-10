import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C039
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard039Part0
open PA215.Contracts PA215.Census

def original4999 : RawOriginal := C039.records[7]'(by decide)
theorem original_id4999 : original4999.index = 4999 := by decide

def c4999 : Contract := original4999.toContract.get (by decide)
theorem binding4999 : original4999.toContract = some c4999 := rfl

theorem checked4999 : check 4000 c4999 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5000 : RawOriginal := C039.records[8]'(by decide)
theorem original_id5000 : original5000.index = 5000 := by decide

def c5000 : Contract := original5000.toContract.get (by decide)
theorem binding5000 : original5000.toContract = some c5000 := rfl

theorem checked5000 : check 4000 c5000 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5001 : RawOriginal := C039.records[9]'(by decide)
theorem original_id5001 : original5001.index = 5001 := by decide

def c5001 : Contract := original5001.toContract.get (by decide)
theorem binding5001 : original5001.toContract = some c5001 := rfl

theorem checked5001 : check 4000 c5001 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5002 : RawOriginal := C039.records[10]'(by decide)
theorem original_id5002 : original5002.index = 5002 := by decide

def c5002 : Contract := original5002.toContract.get (by decide)
theorem binding5002 : original5002.toContract = some c5002 := rfl

theorem checked5002 : check 4000 c5002 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5003 : RawOriginal := C039.records[11]'(by decide)
theorem original_id5003 : original5003.index = 5003 := by decide

def c5003 : Contract := original5003.toContract.get (by decide)
theorem binding5003 : original5003.toContract = some c5003 := rfl

theorem checked5003 : check 4000 c5003 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5004 : RawOriginal := C039.records[12]'(by decide)
theorem original_id5004 : original5004.index = 5004 := by decide

def c5004 : Contract := original5004.toContract.get (by decide)
theorem binding5004 : original5004.toContract = some c5004 := rfl

theorem checked5004 : check 4000 c5004 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5005 : RawOriginal := C039.records[13]'(by decide)
theorem original_id5005 : original5005.index = 5005 := by decide

def c5005 : Contract := original5005.toContract.get (by decide)
theorem binding5005 : original5005.toContract = some c5005 := rfl

theorem checked5005 : check 4000 c5005 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5006 : RawOriginal := C039.records[14]'(by decide)
theorem original_id5006 : original5006.index = 5006 := by decide

def c5006 : Contract := original5006.toContract.get (by decide)
theorem binding5006 : original5006.toContract = some c5006 := rfl

theorem checked5006 : check 4000 c5006 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5007 : RawOriginal := C039.records[15]'(by decide)
theorem original_id5007 : original5007.index = 5007 := by decide

def c5007 : Contract := original5007.toContract.get (by decide)
theorem binding5007 : original5007.toContract = some c5007 := rfl

theorem checked5007 : check 4000 c5007 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5008 : RawOriginal := C039.records[16]'(by decide)
theorem original_id5008 : original5008.index = 5008 := by decide

def c5008 : Contract := original5008.toContract.get (by decide)
theorem binding5008 : original5008.toContract = some c5008 := rfl

theorem checked5008 : check 4000 c5008 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5009 : RawOriginal := C039.records[17]'(by decide)
theorem original_id5009 : original5009.index = 5009 := by decide

def c5009 : Contract := original5009.toContract.get (by decide)
theorem binding5009 : original5009.toContract = some c5009 := rfl

theorem checked5009 : check 4000 c5009 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5010 : RawOriginal := C039.records[18]'(by decide)
theorem original_id5010 : original5010.index = 5010 := by decide

def c5010 : Contract := original5010.toContract.get (by decide)
theorem binding5010 : original5010.toContract = some c5010 := rfl

theorem checked5010 : check 4000 c5010 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5011 : RawOriginal := C039.records[19]'(by decide)
theorem original_id5011 : original5011.index = 5011 := by decide

def c5011 : Contract := original5011.toContract.get (by decide)
theorem binding5011 : original5011.toContract = some c5011 := rfl

theorem checked5011 : check 4000 c5011 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5012 : RawOriginal := C039.records[20]'(by decide)
theorem original_id5012 : original5012.index = 5012 := by decide

def c5012 : Contract := original5012.toContract.get (by decide)
theorem binding5012 : original5012.toContract = some c5012 := rfl

theorem checked5012 : check 4000 c5012 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5013 : RawOriginal := C039.records[21]'(by decide)
theorem original_id5013 : original5013.index = 5013 := by decide

def c5013 : Contract := original5013.toContract.get (by decide)
theorem binding5013 : original5013.toContract = some c5013 := rfl

theorem checked5013 : check 4000 c5013 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5014 : RawOriginal := C039.records[22]'(by decide)
theorem original_id5014 : original5014.index = 5014 := by decide

def c5014 : Contract := original5014.toContract.get (by decide)
theorem binding5014 : original5014.toContract = some c5014 := rfl

theorem checked5014 : check 4000 c5014 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4999, c4999, 4000, checked4999⟩,
  ⟨5000, c5000, 4000, checked5000⟩,
  ⟨5001, c5001, 4000, checked5001⟩,
  ⟨5002, c5002, 4000, checked5002⟩,
  ⟨5003, c5003, 4000, checked5003⟩,
  ⟨5004, c5004, 4000, checked5004⟩,
  ⟨5005, c5005, 4000, checked5005⟩,
  ⟨5006, c5006, 4000, checked5006⟩,
  ⟨5007, c5007, 4000, checked5007⟩,
  ⟨5008, c5008, 4000, checked5008⟩,
  ⟨5009, c5009, 4000, checked5009⟩,
  ⟨5010, c5010, 4000, checked5010⟩,
  ⟨5011, c5011, 4000, checked5011⟩,
  ⟨5012, c5012, 4000, checked5012⟩,
  ⟨5013, c5013, 4000, checked5013⟩,
  ⟨5014, c5014, 4000, checked5014⟩]

end PA215.ContractShards.Shard039Part0
