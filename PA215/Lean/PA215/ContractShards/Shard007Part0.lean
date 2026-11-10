import PA215.CertifiedContracts
import PA215.Census.C007
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard007Part0
open PA215.Contracts PA215.Census

def original902 : RawOriginal := C007.records[6]'(by decide)
theorem original_id902 : original902.index = 902 := by decide

def c902 : Contract := original902.toContract.get (by decide)
theorem binding902 : original902.toContract = some c902 := rfl

theorem checked902 : check 4000 c902 = true := by decide

def original903 : RawOriginal := C007.records[7]'(by decide)
theorem original_id903 : original903.index = 903 := by decide

def c903 : Contract := original903.toContract.get (by decide)
theorem binding903 : original903.toContract = some c903 := rfl

theorem checked903 : check 4000 c903 = true := by decide

def original904 : RawOriginal := C007.records[8]'(by decide)
theorem original_id904 : original904.index = 904 := by decide

def c904 : Contract := original904.toContract.get (by decide)
theorem binding904 : original904.toContract = some c904 := rfl

theorem checked904 : check 4000 c904 = true := by decide

def original905 : RawOriginal := C007.records[9]'(by decide)
theorem original_id905 : original905.index = 905 := by decide

def c905 : Contract := original905.toContract.get (by decide)
theorem binding905 : original905.toContract = some c905 := rfl

theorem checked905 : check 4000 c905 = true := by decide

def original906 : RawOriginal := C007.records[10]'(by decide)
theorem original_id906 : original906.index = 906 := by decide

def c906 : Contract := original906.toContract.get (by decide)
theorem binding906 : original906.toContract = some c906 := rfl

theorem checked906 : check 4000 c906 = true := by decide

def original907 : RawOriginal := C007.records[11]'(by decide)
theorem original_id907 : original907.index = 907 := by decide

def c907 : Contract := original907.toContract.get (by decide)
theorem binding907 : original907.toContract = some c907 := rfl

theorem checked907 : check 4000 c907 = true := by decide

def original908 : RawOriginal := C007.records[12]'(by decide)
theorem original_id908 : original908.index = 908 := by decide

def c908 : Contract := original908.toContract.get (by decide)
theorem binding908 : original908.toContract = some c908 := rfl

theorem checked908 : check 4000 c908 = true := by decide

def original909 : RawOriginal := C007.records[13]'(by decide)
theorem original_id909 : original909.index = 909 := by decide

def c909 : Contract := original909.toContract.get (by decide)
theorem binding909 : original909.toContract = some c909 := rfl

theorem checked909 : check 4000 c909 = true := by decide

def original910 : RawOriginal := C007.records[14]'(by decide)
theorem original_id910 : original910.index = 910 := by decide

def c910 : Contract := original910.toContract.get (by decide)
theorem binding910 : original910.toContract = some c910 := rfl

theorem checked910 : check 4000 c910 = true := by decide

def original911 : RawOriginal := C007.records[15]'(by decide)
theorem original_id911 : original911.index = 911 := by decide

def c911 : Contract := original911.toContract.get (by decide)
theorem binding911 : original911.toContract = some c911 := rfl

theorem checked911 : check 4000 c911 = true := by decide

def original912 : RawOriginal := C007.records[16]'(by decide)
theorem original_id912 : original912.index = 912 := by decide

def c912 : Contract := original912.toContract.get (by decide)
theorem binding912 : original912.toContract = some c912 := rfl

theorem checked912 : check 4000 c912 = true := by decide

def original913 : RawOriginal := C007.records[17]'(by decide)
theorem original_id913 : original913.index = 913 := by decide

def c913 : Contract := original913.toContract.get (by decide)
theorem binding913 : original913.toContract = some c913 := rfl

theorem checked913 : check 4000 c913 = true := by decide

def original914 : RawOriginal := C007.records[18]'(by decide)
theorem original_id914 : original914.index = 914 := by decide

def c914 : Contract := original914.toContract.get (by decide)
theorem binding914 : original914.toContract = some c914 := rfl

theorem checked914 : check 4000 c914 = true := by decide

def original915 : RawOriginal := C007.records[19]'(by decide)
theorem original_id915 : original915.index = 915 := by decide

def c915 : Contract := original915.toContract.get (by decide)
theorem binding915 : original915.toContract = some c915 := rfl

theorem checked915 : check 4000 c915 = true := by decide

def original916 : RawOriginal := C007.records[20]'(by decide)
theorem original_id916 : original916.index = 916 := by decide

def c916 : Contract := original916.toContract.get (by decide)
theorem binding916 : original916.toContract = some c916 := rfl

theorem checked916 : check 4000 c916 = true := by decide

def original917 : RawOriginal := C007.records[21]'(by decide)
theorem original_id917 : original917.index = 917 := by decide

def c917 : Contract := original917.toContract.get (by decide)
theorem binding917 : original917.toContract = some c917 := rfl

theorem checked917 : check 4000 c917 = true := by decide

def records : List Certified := [
  ⟨902, c902, 4000, checked902⟩,
  ⟨903, c903, 4000, checked903⟩,
  ⟨904, c904, 4000, checked904⟩,
  ⟨905, c905, 4000, checked905⟩,
  ⟨906, c906, 4000, checked906⟩,
  ⟨907, c907, 4000, checked907⟩,
  ⟨908, c908, 4000, checked908⟩,
  ⟨909, c909, 4000, checked909⟩,
  ⟨910, c910, 4000, checked910⟩,
  ⟨911, c911, 4000, checked911⟩,
  ⟨912, c912, 4000, checked912⟩,
  ⟨913, c913, 4000, checked913⟩,
  ⟨914, c914, 4000, checked914⟩,
  ⟨915, c915, 4000, checked915⟩,
  ⟨916, c916, 4000, checked916⟩,
  ⟨917, c917, 4000, checked917⟩]

end PA215.ContractShards.Shard007Part0
