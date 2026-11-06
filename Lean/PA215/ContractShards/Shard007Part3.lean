import PA215.CertifiedContracts
import PA215.Census.C007
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard007Part3
open PA215.Contracts PA215.Census

def original950 : RawOriginal := C007.records[54]'(by decide)
theorem original_id950 : original950.index = 950 := by decide

def c950 : Contract := original950.toContract.get (by decide)
theorem binding950 : original950.toContract = some c950 := rfl

theorem checked950 : check 4000 c950 = true := by decide

def original951 : RawOriginal := C007.records[55]'(by decide)
theorem original_id951 : original951.index = 951 := by decide

def c951 : Contract := original951.toContract.get (by decide)
theorem binding951 : original951.toContract = some c951 := rfl

theorem checked951 : check 4000 c951 = true := by decide

def original952 : RawOriginal := C007.records[56]'(by decide)
theorem original_id952 : original952.index = 952 := by decide

def c952 : Contract := original952.toContract.get (by decide)
theorem binding952 : original952.toContract = some c952 := rfl

theorem checked952 : check 4000 c952 = true := by decide

def original953 : RawOriginal := C007.records[57]'(by decide)
theorem original_id953 : original953.index = 953 := by decide

def c953 : Contract := original953.toContract.get (by decide)
theorem binding953 : original953.toContract = some c953 := rfl

theorem checked953 : check 4000 c953 = true := by decide

def original954 : RawOriginal := C007.records[58]'(by decide)
theorem original_id954 : original954.index = 954 := by decide

def c954 : Contract := original954.toContract.get (by decide)
theorem binding954 : original954.toContract = some c954 := rfl

theorem checked954 : check 4000 c954 = true := by decide

def original955 : RawOriginal := C007.records[59]'(by decide)
theorem original_id955 : original955.index = 955 := by decide

def c955 : Contract := original955.toContract.get (by decide)
theorem binding955 : original955.toContract = some c955 := rfl

theorem checked955 : check 4000 c955 = true := by decide

def original956 : RawOriginal := C007.records[60]'(by decide)
theorem original_id956 : original956.index = 956 := by decide

def c956 : Contract := original956.toContract.get (by decide)
theorem binding956 : original956.toContract = some c956 := rfl

theorem checked956 : check 4000 c956 = true := by decide

def original957 : RawOriginal := C007.records[61]'(by decide)
theorem original_id957 : original957.index = 957 := by decide

def c957 : Contract := original957.toContract.get (by decide)
theorem binding957 : original957.toContract = some c957 := rfl

theorem checked957 : check 4000 c957 = true := by decide

def original958 : RawOriginal := C007.records[62]'(by decide)
theorem original_id958 : original958.index = 958 := by decide

def c958 : Contract := original958.toContract.get (by decide)
theorem binding958 : original958.toContract = some c958 := rfl

theorem checked958 : check 4000 c958 = true := by decide

def original959 : RawOriginal := C007.records[63]'(by decide)
theorem original_id959 : original959.index = 959 := by decide

def c959 : Contract := original959.toContract.get (by decide)
theorem binding959 : original959.toContract = some c959 := rfl

theorem checked959 : check 4000 c959 = true := by decide

def original960 : RawOriginal := C007.records[64]'(by decide)
theorem original_id960 : original960.index = 960 := by decide

def c960 : Contract := original960.toContract.get (by decide)
theorem binding960 : original960.toContract = some c960 := rfl

theorem checked960 : check 4000 c960 = true := by decide

def original961 : RawOriginal := C007.records[65]'(by decide)
theorem original_id961 : original961.index = 961 := by decide

def c961 : Contract := original961.toContract.get (by decide)
theorem binding961 : original961.toContract = some c961 := rfl

theorem checked961 : check 4000 c961 = true := by decide

def original962 : RawOriginal := C007.records[66]'(by decide)
theorem original_id962 : original962.index = 962 := by decide

def c962 : Contract := original962.toContract.get (by decide)
theorem binding962 : original962.toContract = some c962 := rfl

theorem checked962 : check 4000 c962 = true := by decide

def original963 : RawOriginal := C007.records[67]'(by decide)
theorem original_id963 : original963.index = 963 := by decide

def c963 : Contract := original963.toContract.get (by decide)
theorem binding963 : original963.toContract = some c963 := rfl

theorem checked963 : check 4000 c963 = true := by decide

def original964 : RawOriginal := C007.records[68]'(by decide)
theorem original_id964 : original964.index = 964 := by decide

def c964 : Contract := original964.toContract.get (by decide)
theorem binding964 : original964.toContract = some c964 := rfl

theorem checked964 : check 4000 c964 = true := by decide

def original965 : RawOriginal := C007.records[69]'(by decide)
theorem original_id965 : original965.index = 965 := by decide

def c965 : Contract := original965.toContract.get (by decide)
theorem binding965 : original965.toContract = some c965 := rfl

theorem checked965 : check 4000 c965 = true := by decide

def records : List Certified := [
  ⟨950, c950, 4000, checked950⟩,
  ⟨951, c951, 4000, checked951⟩,
  ⟨952, c952, 4000, checked952⟩,
  ⟨953, c953, 4000, checked953⟩,
  ⟨954, c954, 4000, checked954⟩,
  ⟨955, c955, 4000, checked955⟩,
  ⟨956, c956, 4000, checked956⟩,
  ⟨957, c957, 4000, checked957⟩,
  ⟨958, c958, 4000, checked958⟩,
  ⟨959, c959, 4000, checked959⟩,
  ⟨960, c960, 4000, checked960⟩,
  ⟨961, c961, 4000, checked961⟩,
  ⟨962, c962, 4000, checked962⟩,
  ⟨963, c963, 4000, checked963⟩,
  ⟨964, c964, 4000, checked964⟩,
  ⟨965, c965, 4000, checked965⟩]

end PA215.ContractShards.Shard007Part3
