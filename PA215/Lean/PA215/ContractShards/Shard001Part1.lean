import PA215.CertifiedContracts
import PA215.Census.C001
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard001Part1
open PA215.Contracts PA215.Census

def original150 : RawOriginal := C001.records[22]'(by decide)
theorem original_id150 : original150.index = 150 := by decide

def c150 : Contract := original150.toContract.get (by decide)
theorem binding150 : original150.toContract = some c150 := rfl

theorem checked150 : check 4000 c150 = true := by decide

def original151 : RawOriginal := C001.records[23]'(by decide)
theorem original_id151 : original151.index = 151 := by decide

def c151 : Contract := original151.toContract.get (by decide)
theorem binding151 : original151.toContract = some c151 := rfl

theorem checked151 : check 4000 c151 = true := by decide

def original152 : RawOriginal := C001.records[24]'(by decide)
theorem original_id152 : original152.index = 152 := by decide

def c152 : Contract := original152.toContract.get (by decide)
theorem binding152 : original152.toContract = some c152 := rfl

theorem checked152 : check 4000 c152 = true := by decide

def original153 : RawOriginal := C001.records[25]'(by decide)
theorem original_id153 : original153.index = 153 := by decide

def c153 : Contract := original153.toContract.get (by decide)
theorem binding153 : original153.toContract = some c153 := rfl

theorem checked153 : check 4000 c153 = true := by decide

def original154 : RawOriginal := C001.records[26]'(by decide)
theorem original_id154 : original154.index = 154 := by decide

def c154 : Contract := original154.toContract.get (by decide)
theorem binding154 : original154.toContract = some c154 := rfl

theorem checked154 : check 4000 c154 = true := by decide

def original155 : RawOriginal := C001.records[27]'(by decide)
theorem original_id155 : original155.index = 155 := by decide

def c155 : Contract := original155.toContract.get (by decide)
theorem binding155 : original155.toContract = some c155 := rfl

theorem checked155 : check 4000 c155 = true := by decide

def original156 : RawOriginal := C001.records[28]'(by decide)
theorem original_id156 : original156.index = 156 := by decide

def c156 : Contract := original156.toContract.get (by decide)
theorem binding156 : original156.toContract = some c156 := rfl

theorem checked156 : check 4000 c156 = true := by decide

def original157 : RawOriginal := C001.records[29]'(by decide)
theorem original_id157 : original157.index = 157 := by decide

def c157 : Contract := original157.toContract.get (by decide)
theorem binding157 : original157.toContract = some c157 := rfl

theorem checked157 : check 4000 c157 = true := by decide

def original158 : RawOriginal := C001.records[30]'(by decide)
theorem original_id158 : original158.index = 158 := by decide

def c158 : Contract := original158.toContract.get (by decide)
theorem binding158 : original158.toContract = some c158 := rfl

theorem checked158 : check 4000 c158 = true := by decide

def original159 : RawOriginal := C001.records[31]'(by decide)
theorem original_id159 : original159.index = 159 := by decide

def c159 : Contract := original159.toContract.get (by decide)
theorem binding159 : original159.toContract = some c159 := rfl

theorem checked159 : check 4000 c159 = true := by decide

def original160 : RawOriginal := C001.records[32]'(by decide)
theorem original_id160 : original160.index = 160 := by decide

def c160 : Contract := original160.toContract.get (by decide)
theorem binding160 : original160.toContract = some c160 := rfl

theorem checked160 : check 4000 c160 = true := by decide

def original161 : RawOriginal := C001.records[33]'(by decide)
theorem original_id161 : original161.index = 161 := by decide

def c161 : Contract := original161.toContract.get (by decide)
theorem binding161 : original161.toContract = some c161 := rfl

theorem checked161 : check 4000 c161 = true := by decide

def original162 : RawOriginal := C001.records[34]'(by decide)
theorem original_id162 : original162.index = 162 := by decide

def c162 : Contract := original162.toContract.get (by decide)
theorem binding162 : original162.toContract = some c162 := rfl

theorem checked162 : check 4000 c162 = true := by decide

def original163 : RawOriginal := C001.records[35]'(by decide)
theorem original_id163 : original163.index = 163 := by decide

def c163 : Contract := original163.toContract.get (by decide)
theorem binding163 : original163.toContract = some c163 := rfl

theorem checked163 : check 4000 c163 = true := by decide

def original164 : RawOriginal := C001.records[36]'(by decide)
theorem original_id164 : original164.index = 164 := by decide

def c164 : Contract := original164.toContract.get (by decide)
theorem binding164 : original164.toContract = some c164 := rfl

theorem checked164 : check 4000 c164 = true := by decide

def original165 : RawOriginal := C001.records[37]'(by decide)
theorem original_id165 : original165.index = 165 := by decide

def c165 : Contract := original165.toContract.get (by decide)
theorem binding165 : original165.toContract = some c165 := rfl

theorem checked165 : check 4000 c165 = true := by decide

def records : List Certified := [
  ⟨150, c150, 4000, checked150⟩,
  ⟨151, c151, 4000, checked151⟩,
  ⟨152, c152, 4000, checked152⟩,
  ⟨153, c153, 4000, checked153⟩,
  ⟨154, c154, 4000, checked154⟩,
  ⟨155, c155, 4000, checked155⟩,
  ⟨156, c156, 4000, checked156⟩,
  ⟨157, c157, 4000, checked157⟩,
  ⟨158, c158, 4000, checked158⟩,
  ⟨159, c159, 4000, checked159⟩,
  ⟨160, c160, 4000, checked160⟩,
  ⟨161, c161, 4000, checked161⟩,
  ⟨162, c162, 4000, checked162⟩,
  ⟨163, c163, 4000, checked163⟩,
  ⟨164, c164, 4000, checked164⟩,
  ⟨165, c165, 4000, checked165⟩]

end PA215.ContractShards.Shard001Part1
