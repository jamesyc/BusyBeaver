import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C031
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard031Part2
open PA215.Contracts PA215.Census

def original4006 : RawOriginal := C031.records[38]'(by decide)
theorem original_id4006 : original4006.index = 4006 := by decide

def c4006 : Contract := original4006.toContract.get (by decide)
theorem binding4006 : original4006.toContract = some c4006 := rfl

theorem checked4006 : check 4000 c4006 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4007 : RawOriginal := C031.records[39]'(by decide)
theorem original_id4007 : original4007.index = 4007 := by decide

def c4007 : Contract := original4007.toContract.get (by decide)
theorem binding4007 : original4007.toContract = some c4007 := rfl

theorem checked4007 : check 4000 c4007 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4008 : RawOriginal := C031.records[40]'(by decide)
theorem original_id4008 : original4008.index = 4008 := by decide

def c4008 : Contract := original4008.toContract.get (by decide)
theorem binding4008 : original4008.toContract = some c4008 := rfl

theorem checked4008 : check 4000 c4008 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4009 : RawOriginal := C031.records[41]'(by decide)
theorem original_id4009 : original4009.index = 4009 := by decide

def c4009 : Contract := original4009.toContract.get (by decide)
theorem binding4009 : original4009.toContract = some c4009 := rfl

theorem checked4009 : check 4000 c4009 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4010 : RawOriginal := C031.records[42]'(by decide)
theorem original_id4010 : original4010.index = 4010 := by decide

def c4010 : Contract := original4010.toContract.get (by decide)
theorem binding4010 : original4010.toContract = some c4010 := rfl

theorem checked4010 : check 4000 c4010 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4011 : RawOriginal := C031.records[43]'(by decide)
theorem original_id4011 : original4011.index = 4011 := by decide

def c4011 : Contract := original4011.toContract.get (by decide)
theorem binding4011 : original4011.toContract = some c4011 := rfl

theorem checked4011 : check 4000 c4011 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4012 : RawOriginal := C031.records[44]'(by decide)
theorem original_id4012 : original4012.index = 4012 := by decide

def c4012 : Contract := original4012.toContract.get (by decide)
theorem binding4012 : original4012.toContract = some c4012 := rfl

theorem checked4012 : check 4000 c4012 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4013 : RawOriginal := C031.records[45]'(by decide)
theorem original_id4013 : original4013.index = 4013 := by decide

def c4013 : Contract := original4013.toContract.get (by decide)
theorem binding4013 : original4013.toContract = some c4013 := rfl

theorem checked4013 : check 4000 c4013 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4014 : RawOriginal := C031.records[46]'(by decide)
theorem original_id4014 : original4014.index = 4014 := by decide

def c4014 : Contract := original4014.toContract.get (by decide)
theorem binding4014 : original4014.toContract = some c4014 := rfl

theorem checked4014 : check 4000 c4014 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4015 : RawOriginal := C031.records[47]'(by decide)
theorem original_id4015 : original4015.index = 4015 := by decide

def c4015 : Contract := original4015.toContract.get (by decide)
theorem binding4015 : original4015.toContract = some c4015 := rfl

theorem checked4015 : check 4000 c4015 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4016 : RawOriginal := C031.records[48]'(by decide)
theorem original_id4016 : original4016.index = 4016 := by decide

def c4016 : Contract := original4016.toContract.get (by decide)
theorem binding4016 : original4016.toContract = some c4016 := rfl

theorem checked4016 : check 4000 c4016 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4017 : RawOriginal := C031.records[49]'(by decide)
theorem original_id4017 : original4017.index = 4017 := by decide

def c4017 : Contract := original4017.toContract.get (by decide)
theorem binding4017 : original4017.toContract = some c4017 := rfl

theorem checked4017 : check 4000 c4017 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4018 : RawOriginal := C031.records[50]'(by decide)
theorem original_id4018 : original4018.index = 4018 := by decide

def c4018 : Contract := original4018.toContract.get (by decide)
theorem binding4018 : original4018.toContract = some c4018 := rfl

theorem checked4018 : check 4000 c4018 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4019 : RawOriginal := C031.records[51]'(by decide)
theorem original_id4019 : original4019.index = 4019 := by decide

def c4019 : Contract := original4019.toContract.get (by decide)
theorem binding4019 : original4019.toContract = some c4019 := rfl

theorem checked4019 : check 4000 c4019 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4020 : RawOriginal := C031.records[52]'(by decide)
theorem original_id4020 : original4020.index = 4020 := by decide

def c4020 : Contract := original4020.toContract.get (by decide)
theorem binding4020 : original4020.toContract = some c4020 := rfl

theorem checked4020 : check 4000 c4020 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4021 : RawOriginal := C031.records[53]'(by decide)
theorem original_id4021 : original4021.index = 4021 := by decide

def c4021 : Contract := original4021.toContract.get (by decide)
theorem binding4021 : original4021.toContract = some c4021 := rfl

theorem checked4021 : check 4000 c4021 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4006, c4006, 4000, checked4006⟩,
  ⟨4007, c4007, 4000, checked4007⟩,
  ⟨4008, c4008, 4000, checked4008⟩,
  ⟨4009, c4009, 4000, checked4009⟩,
  ⟨4010, c4010, 4000, checked4010⟩,
  ⟨4011, c4011, 4000, checked4011⟩,
  ⟨4012, c4012, 4000, checked4012⟩,
  ⟨4013, c4013, 4000, checked4013⟩,
  ⟨4014, c4014, 4000, checked4014⟩,
  ⟨4015, c4015, 4000, checked4015⟩,
  ⟨4016, c4016, 4000, checked4016⟩,
  ⟨4017, c4017, 4000, checked4017⟩,
  ⟨4018, c4018, 4000, checked4018⟩,
  ⟨4019, c4019, 4000, checked4019⟩,
  ⟨4020, c4020, 4000, checked4020⟩,
  ⟨4021, c4021, 4000, checked4021⟩]

end PA215.ContractShards.Shard031Part2
