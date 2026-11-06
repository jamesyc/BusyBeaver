import PA215.CertifiedContracts
import PA215.Census.C007
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard007Part5
open PA215.Contracts PA215.Census

def original982 : RawOriginal := C007.records[86]'(by decide)
theorem original_id982 : original982.index = 982 := by decide

def c982 : Contract := original982.toContract.get (by decide)
theorem binding982 : original982.toContract = some c982 := rfl

theorem checked982 : check 4000 c982 = true := by decide

def original983 : RawOriginal := C007.records[87]'(by decide)
theorem original_id983 : original983.index = 983 := by decide

def c983 : Contract := original983.toContract.get (by decide)
theorem binding983 : original983.toContract = some c983 := rfl

theorem checked983 : check 4000 c983 = true := by decide

def original984 : RawOriginal := C007.records[88]'(by decide)
theorem original_id984 : original984.index = 984 := by decide

def c984 : Contract := original984.toContract.get (by decide)
theorem binding984 : original984.toContract = some c984 := rfl

theorem checked984 : check 4000 c984 = true := by decide

def original985 : RawOriginal := C007.records[89]'(by decide)
theorem original_id985 : original985.index = 985 := by decide

def c985 : Contract := original985.toContract.get (by decide)
theorem binding985 : original985.toContract = some c985 := rfl

theorem checked985 : check 4000 c985 = true := by decide

def original986 : RawOriginal := C007.records[90]'(by decide)
theorem original_id986 : original986.index = 986 := by decide

def c986 : Contract := original986.toContract.get (by decide)
theorem binding986 : original986.toContract = some c986 := rfl

theorem checked986 : check 4000 c986 = true := by decide

def original987 : RawOriginal := C007.records[91]'(by decide)
theorem original_id987 : original987.index = 987 := by decide

def c987 : Contract := original987.toContract.get (by decide)
theorem binding987 : original987.toContract = some c987 := rfl

theorem checked987 : check 4000 c987 = true := by decide

def original988 : RawOriginal := C007.records[92]'(by decide)
theorem original_id988 : original988.index = 988 := by decide

def c988 : Contract := original988.toContract.get (by decide)
theorem binding988 : original988.toContract = some c988 := rfl

theorem checked988 : check 4000 c988 = true := by decide

def original989 : RawOriginal := C007.records[93]'(by decide)
theorem original_id989 : original989.index = 989 := by decide

def c989 : Contract := original989.toContract.get (by decide)
theorem binding989 : original989.toContract = some c989 := rfl

theorem checked989 : check 4000 c989 = true := by decide

def original990 : RawOriginal := C007.records[94]'(by decide)
theorem original_id990 : original990.index = 990 := by decide

def c990 : Contract := original990.toContract.get (by decide)
theorem binding990 : original990.toContract = some c990 := rfl

theorem checked990 : check 4000 c990 = true := by decide

def original991 : RawOriginal := C007.records[95]'(by decide)
theorem original_id991 : original991.index = 991 := by decide

def c991 : Contract := original991.toContract.get (by decide)
theorem binding991 : original991.toContract = some c991 := rfl

theorem checked991 : check 4000 c991 = true := by decide

def original992 : RawOriginal := C007.records[96]'(by decide)
theorem original_id992 : original992.index = 992 := by decide

def c992 : Contract := original992.toContract.get (by decide)
theorem binding992 : original992.toContract = some c992 := rfl

theorem checked992 : check 4000 c992 = true := by decide

def original993 : RawOriginal := C007.records[97]'(by decide)
theorem original_id993 : original993.index = 993 := by decide

def c993 : Contract := original993.toContract.get (by decide)
theorem binding993 : original993.toContract = some c993 := rfl

theorem checked993 : check 4000 c993 = true := by decide

def original994 : RawOriginal := C007.records[98]'(by decide)
theorem original_id994 : original994.index = 994 := by decide

def c994 : Contract := original994.toContract.get (by decide)
theorem binding994 : original994.toContract = some c994 := rfl

theorem checked994 : check 4000 c994 = true := by decide

def original995 : RawOriginal := C007.records[99]'(by decide)
theorem original_id995 : original995.index = 995 := by decide

def c995 : Contract := original995.toContract.get (by decide)
theorem binding995 : original995.toContract = some c995 := rfl

theorem checked995 : check 4000 c995 = true := by decide

def original996 : RawOriginal := C007.records[100]'(by decide)
theorem original_id996 : original996.index = 996 := by decide

def c996 : Contract := original996.toContract.get (by decide)
theorem binding996 : original996.toContract = some c996 := rfl

theorem checked996 : check 4000 c996 = true := by decide

def original997 : RawOriginal := C007.records[101]'(by decide)
theorem original_id997 : original997.index = 997 := by decide

def c997 : Contract := original997.toContract.get (by decide)
theorem binding997 : original997.toContract = some c997 := rfl

theorem checked997 : check 4000 c997 = true := by decide

def records : List Certified := [
  ⟨982, c982, 4000, checked982⟩,
  ⟨983, c983, 4000, checked983⟩,
  ⟨984, c984, 4000, checked984⟩,
  ⟨985, c985, 4000, checked985⟩,
  ⟨986, c986, 4000, checked986⟩,
  ⟨987, c987, 4000, checked987⟩,
  ⟨988, c988, 4000, checked988⟩,
  ⟨989, c989, 4000, checked989⟩,
  ⟨990, c990, 4000, checked990⟩,
  ⟨991, c991, 4000, checked991⟩,
  ⟨992, c992, 4000, checked992⟩,
  ⟨993, c993, 4000, checked993⟩,
  ⟨994, c994, 4000, checked994⟩,
  ⟨995, c995, 4000, checked995⟩,
  ⟨996, c996, 4000, checked996⟩,
  ⟨997, c997, 4000, checked997⟩]

end PA215.ContractShards.Shard007Part5
