import PA215.CertifiedContracts
import PA215.Census.C007
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard007Part4
open PA215.Contracts PA215.Census

def original966 : RawOriginal := C007.records[70]'(by decide)
theorem original_id966 : original966.index = 966 := by decide

def c966 : Contract := original966.toContract.get (by decide)
theorem binding966 : original966.toContract = some c966 := rfl

theorem checked966 : check 4000 c966 = true := by decide

def original967 : RawOriginal := C007.records[71]'(by decide)
theorem original_id967 : original967.index = 967 := by decide

def c967 : Contract := original967.toContract.get (by decide)
theorem binding967 : original967.toContract = some c967 := rfl

theorem checked967 : check 4000 c967 = true := by decide

def original968 : RawOriginal := C007.records[72]'(by decide)
theorem original_id968 : original968.index = 968 := by decide

def c968 : Contract := original968.toContract.get (by decide)
theorem binding968 : original968.toContract = some c968 := rfl

theorem checked968 : check 4000 c968 = true := by decide

def original969 : RawOriginal := C007.records[73]'(by decide)
theorem original_id969 : original969.index = 969 := by decide

def c969 : Contract := original969.toContract.get (by decide)
theorem binding969 : original969.toContract = some c969 := rfl

theorem checked969 : check 4000 c969 = true := by decide

def original970 : RawOriginal := C007.records[74]'(by decide)
theorem original_id970 : original970.index = 970 := by decide

def c970 : Contract := original970.toContract.get (by decide)
theorem binding970 : original970.toContract = some c970 := rfl

theorem checked970 : check 4000 c970 = true := by decide

def original971 : RawOriginal := C007.records[75]'(by decide)
theorem original_id971 : original971.index = 971 := by decide

def c971 : Contract := original971.toContract.get (by decide)
theorem binding971 : original971.toContract = some c971 := rfl

theorem checked971 : check 4000 c971 = true := by decide

def original972 : RawOriginal := C007.records[76]'(by decide)
theorem original_id972 : original972.index = 972 := by decide

def c972 : Contract := original972.toContract.get (by decide)
theorem binding972 : original972.toContract = some c972 := rfl

theorem checked972 : check 4000 c972 = true := by decide

def original973 : RawOriginal := C007.records[77]'(by decide)
theorem original_id973 : original973.index = 973 := by decide

def c973 : Contract := original973.toContract.get (by decide)
theorem binding973 : original973.toContract = some c973 := rfl

theorem checked973 : check 4000 c973 = true := by decide

def original974 : RawOriginal := C007.records[78]'(by decide)
theorem original_id974 : original974.index = 974 := by decide

def c974 : Contract := original974.toContract.get (by decide)
theorem binding974 : original974.toContract = some c974 := rfl

theorem checked974 : check 4000 c974 = true := by decide

def original975 : RawOriginal := C007.records[79]'(by decide)
theorem original_id975 : original975.index = 975 := by decide

def c975 : Contract := original975.toContract.get (by decide)
theorem binding975 : original975.toContract = some c975 := rfl

theorem checked975 : check 4000 c975 = true := by decide

def original976 : RawOriginal := C007.records[80]'(by decide)
theorem original_id976 : original976.index = 976 := by decide

def c976 : Contract := original976.toContract.get (by decide)
theorem binding976 : original976.toContract = some c976 := rfl

theorem checked976 : check 4000 c976 = true := by decide

def original977 : RawOriginal := C007.records[81]'(by decide)
theorem original_id977 : original977.index = 977 := by decide

def c977 : Contract := original977.toContract.get (by decide)
theorem binding977 : original977.toContract = some c977 := rfl

theorem checked977 : check 4000 c977 = true := by decide

def original978 : RawOriginal := C007.records[82]'(by decide)
theorem original_id978 : original978.index = 978 := by decide

def c978 : Contract := original978.toContract.get (by decide)
theorem binding978 : original978.toContract = some c978 := rfl

theorem checked978 : check 4000 c978 = true := by decide

def original979 : RawOriginal := C007.records[83]'(by decide)
theorem original_id979 : original979.index = 979 := by decide

def c979 : Contract := original979.toContract.get (by decide)
theorem binding979 : original979.toContract = some c979 := rfl

theorem checked979 : check 4000 c979 = true := by decide

def original980 : RawOriginal := C007.records[84]'(by decide)
theorem original_id980 : original980.index = 980 := by decide

def c980 : Contract := original980.toContract.get (by decide)
theorem binding980 : original980.toContract = some c980 := rfl

theorem checked980 : check 4000 c980 = true := by decide

def original981 : RawOriginal := C007.records[85]'(by decide)
theorem original_id981 : original981.index = 981 := by decide

def c981 : Contract := original981.toContract.get (by decide)
theorem binding981 : original981.toContract = some c981 := rfl

theorem checked981 : check 4000 c981 = true := by decide

def records : List Certified := [
  ⟨966, c966, 4000, checked966⟩,
  ⟨967, c967, 4000, checked967⟩,
  ⟨968, c968, 4000, checked968⟩,
  ⟨969, c969, 4000, checked969⟩,
  ⟨970, c970, 4000, checked970⟩,
  ⟨971, c971, 4000, checked971⟩,
  ⟨972, c972, 4000, checked972⟩,
  ⟨973, c973, 4000, checked973⟩,
  ⟨974, c974, 4000, checked974⟩,
  ⟨975, c975, 4000, checked975⟩,
  ⟨976, c976, 4000, checked976⟩,
  ⟨977, c977, 4000, checked977⟩,
  ⟨978, c978, 4000, checked978⟩,
  ⟨979, c979, 4000, checked979⟩,
  ⟨980, c980, 4000, checked980⟩,
  ⟨981, c981, 4000, checked981⟩]

end PA215.ContractShards.Shard007Part4
