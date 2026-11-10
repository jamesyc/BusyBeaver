import PA215.CertifiedContracts
import PA215.Census.C007
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard007Part1
open PA215.Contracts PA215.Census

def original918 : RawOriginal := C007.records[22]'(by decide)
theorem original_id918 : original918.index = 918 := by decide

def c918 : Contract := original918.toContract.get (by decide)
theorem binding918 : original918.toContract = some c918 := rfl

theorem checked918 : check 4000 c918 = true := by decide

def original919 : RawOriginal := C007.records[23]'(by decide)
theorem original_id919 : original919.index = 919 := by decide

def c919 : Contract := original919.toContract.get (by decide)
theorem binding919 : original919.toContract = some c919 := rfl

theorem checked919 : check 4000 c919 = true := by decide

def original920 : RawOriginal := C007.records[24]'(by decide)
theorem original_id920 : original920.index = 920 := by decide

def c920 : Contract := original920.toContract.get (by decide)
theorem binding920 : original920.toContract = some c920 := rfl

theorem checked920 : check 4000 c920 = true := by decide

def original921 : RawOriginal := C007.records[25]'(by decide)
theorem original_id921 : original921.index = 921 := by decide

def c921 : Contract := original921.toContract.get (by decide)
theorem binding921 : original921.toContract = some c921 := rfl

theorem checked921 : check 4000 c921 = true := by decide

def original922 : RawOriginal := C007.records[26]'(by decide)
theorem original_id922 : original922.index = 922 := by decide

def c922 : Contract := original922.toContract.get (by decide)
theorem binding922 : original922.toContract = some c922 := rfl

theorem checked922 : check 4000 c922 = true := by decide

def original923 : RawOriginal := C007.records[27]'(by decide)
theorem original_id923 : original923.index = 923 := by decide

def c923 : Contract := original923.toContract.get (by decide)
theorem binding923 : original923.toContract = some c923 := rfl

theorem checked923 : check 4000 c923 = true := by decide

def original924 : RawOriginal := C007.records[28]'(by decide)
theorem original_id924 : original924.index = 924 := by decide

def c924 : Contract := original924.toContract.get (by decide)
theorem binding924 : original924.toContract = some c924 := rfl

theorem checked924 : check 4000 c924 = true := by decide

def original925 : RawOriginal := C007.records[29]'(by decide)
theorem original_id925 : original925.index = 925 := by decide

def c925 : Contract := original925.toContract.get (by decide)
theorem binding925 : original925.toContract = some c925 := rfl

theorem checked925 : check 4000 c925 = true := by decide

def original926 : RawOriginal := C007.records[30]'(by decide)
theorem original_id926 : original926.index = 926 := by decide

def c926 : Contract := original926.toContract.get (by decide)
theorem binding926 : original926.toContract = some c926 := rfl

theorem checked926 : check 4000 c926 = true := by decide

def original927 : RawOriginal := C007.records[31]'(by decide)
theorem original_id927 : original927.index = 927 := by decide

def c927 : Contract := original927.toContract.get (by decide)
theorem binding927 : original927.toContract = some c927 := rfl

theorem checked927 : check 4000 c927 = true := by decide

def original928 : RawOriginal := C007.records[32]'(by decide)
theorem original_id928 : original928.index = 928 := by decide

def c928 : Contract := original928.toContract.get (by decide)
theorem binding928 : original928.toContract = some c928 := rfl

theorem checked928 : check 4000 c928 = true := by decide

def original929 : RawOriginal := C007.records[33]'(by decide)
theorem original_id929 : original929.index = 929 := by decide

def c929 : Contract := original929.toContract.get (by decide)
theorem binding929 : original929.toContract = some c929 := rfl

theorem checked929 : check 4000 c929 = true := by decide

def original930 : RawOriginal := C007.records[34]'(by decide)
theorem original_id930 : original930.index = 930 := by decide

def c930 : Contract := original930.toContract.get (by decide)
theorem binding930 : original930.toContract = some c930 := rfl

theorem checked930 : check 4000 c930 = true := by decide

def original931 : RawOriginal := C007.records[35]'(by decide)
theorem original_id931 : original931.index = 931 := by decide

def c931 : Contract := original931.toContract.get (by decide)
theorem binding931 : original931.toContract = some c931 := rfl

theorem checked931 : check 4000 c931 = true := by decide

def original932 : RawOriginal := C007.records[36]'(by decide)
theorem original_id932 : original932.index = 932 := by decide

def c932 : Contract := original932.toContract.get (by decide)
theorem binding932 : original932.toContract = some c932 := rfl

theorem checked932 : check 4000 c932 = true := by decide

def original933 : RawOriginal := C007.records[37]'(by decide)
theorem original_id933 : original933.index = 933 := by decide

def c933 : Contract := original933.toContract.get (by decide)
theorem binding933 : original933.toContract = some c933 := rfl

theorem checked933 : check 4000 c933 = true := by decide

def records : List Certified := [
  ⟨918, c918, 4000, checked918⟩,
  ⟨919, c919, 4000, checked919⟩,
  ⟨920, c920, 4000, checked920⟩,
  ⟨921, c921, 4000, checked921⟩,
  ⟨922, c922, 4000, checked922⟩,
  ⟨923, c923, 4000, checked923⟩,
  ⟨924, c924, 4000, checked924⟩,
  ⟨925, c925, 4000, checked925⟩,
  ⟨926, c926, 4000, checked926⟩,
  ⟨927, c927, 4000, checked927⟩,
  ⟨928, c928, 4000, checked928⟩,
  ⟨929, c929, 4000, checked929⟩,
  ⟨930, c930, 4000, checked930⟩,
  ⟨931, c931, 4000, checked931⟩,
  ⟨932, c932, 4000, checked932⟩,
  ⟨933, c933, 4000, checked933⟩]

end PA215.ContractShards.Shard007Part1
