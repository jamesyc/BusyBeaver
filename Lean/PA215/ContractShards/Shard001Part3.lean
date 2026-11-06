import PA215.CertifiedContracts
import PA215.Census.C001
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard001Part3
open PA215.Contracts PA215.Census

def original182 : RawOriginal := C001.records[54]'(by decide)
theorem original_id182 : original182.index = 182 := by decide

def c182 : Contract := original182.toContract.get (by decide)
theorem binding182 : original182.toContract = some c182 := rfl

theorem checked182 : check 4000 c182 = true := by decide

def original183 : RawOriginal := C001.records[55]'(by decide)
theorem original_id183 : original183.index = 183 := by decide

def c183 : Contract := original183.toContract.get (by decide)
theorem binding183 : original183.toContract = some c183 := rfl

theorem checked183 : check 4000 c183 = true := by decide

def original184 : RawOriginal := C001.records[56]'(by decide)
theorem original_id184 : original184.index = 184 := by decide

def c184 : Contract := original184.toContract.get (by decide)
theorem binding184 : original184.toContract = some c184 := rfl

theorem checked184 : check 4000 c184 = true := by decide

def original185 : RawOriginal := C001.records[57]'(by decide)
theorem original_id185 : original185.index = 185 := by decide

def c185 : Contract := original185.toContract.get (by decide)
theorem binding185 : original185.toContract = some c185 := rfl

theorem checked185 : check 4000 c185 = true := by decide

def original186 : RawOriginal := C001.records[58]'(by decide)
theorem original_id186 : original186.index = 186 := by decide

def c186 : Contract := original186.toContract.get (by decide)
theorem binding186 : original186.toContract = some c186 := rfl

theorem checked186 : check 4000 c186 = true := by decide

def original187 : RawOriginal := C001.records[59]'(by decide)
theorem original_id187 : original187.index = 187 := by decide

def c187 : Contract := original187.toContract.get (by decide)
theorem binding187 : original187.toContract = some c187 := rfl

theorem checked187 : check 4000 c187 = true := by decide

def original188 : RawOriginal := C001.records[60]'(by decide)
theorem original_id188 : original188.index = 188 := by decide

def c188 : Contract := original188.toContract.get (by decide)
theorem binding188 : original188.toContract = some c188 := rfl

theorem checked188 : check 4000 c188 = true := by decide

def original189 : RawOriginal := C001.records[61]'(by decide)
theorem original_id189 : original189.index = 189 := by decide

def c189 : Contract := original189.toContract.get (by decide)
theorem binding189 : original189.toContract = some c189 := rfl

theorem checked189 : check 4000 c189 = true := by decide

def original190 : RawOriginal := C001.records[62]'(by decide)
theorem original_id190 : original190.index = 190 := by decide

def c190 : Contract := original190.toContract.get (by decide)
theorem binding190 : original190.toContract = some c190 := rfl

theorem checked190 : check 4000 c190 = true := by decide

def original191 : RawOriginal := C001.records[63]'(by decide)
theorem original_id191 : original191.index = 191 := by decide

def c191 : Contract := original191.toContract.get (by decide)
theorem binding191 : original191.toContract = some c191 := rfl

theorem checked191 : check 4000 c191 = true := by decide

def original192 : RawOriginal := C001.records[64]'(by decide)
theorem original_id192 : original192.index = 192 := by decide

def c192 : Contract := original192.toContract.get (by decide)
theorem binding192 : original192.toContract = some c192 := rfl

theorem checked192 : check 4000 c192 = true := by decide

def original193 : RawOriginal := C001.records[65]'(by decide)
theorem original_id193 : original193.index = 193 := by decide

def c193 : Contract := original193.toContract.get (by decide)
theorem binding193 : original193.toContract = some c193 := rfl

theorem checked193 : check 4000 c193 = true := by decide

def original194 : RawOriginal := C001.records[66]'(by decide)
theorem original_id194 : original194.index = 194 := by decide

def c194 : Contract := original194.toContract.get (by decide)
theorem binding194 : original194.toContract = some c194 := rfl

theorem checked194 : check 4000 c194 = true := by decide

def original195 : RawOriginal := C001.records[67]'(by decide)
theorem original_id195 : original195.index = 195 := by decide

def c195 : Contract := original195.toContract.get (by decide)
theorem binding195 : original195.toContract = some c195 := rfl

theorem checked195 : check 4000 c195 = true := by decide

def original196 : RawOriginal := C001.records[68]'(by decide)
theorem original_id196 : original196.index = 196 := by decide

def c196 : Contract := original196.toContract.get (by decide)
theorem binding196 : original196.toContract = some c196 := rfl

theorem checked196 : check 4000 c196 = true := by decide

def original197 : RawOriginal := C001.records[69]'(by decide)
theorem original_id197 : original197.index = 197 := by decide

def c197 : Contract := original197.toContract.get (by decide)
theorem binding197 : original197.toContract = some c197 := rfl

theorem checked197 : check 4000 c197 = true := by decide

def records : List Certified := [
  ⟨182, c182, 4000, checked182⟩,
  ⟨183, c183, 4000, checked183⟩,
  ⟨184, c184, 4000, checked184⟩,
  ⟨185, c185, 4000, checked185⟩,
  ⟨186, c186, 4000, checked186⟩,
  ⟨187, c187, 4000, checked187⟩,
  ⟨188, c188, 4000, checked188⟩,
  ⟨189, c189, 4000, checked189⟩,
  ⟨190, c190, 4000, checked190⟩,
  ⟨191, c191, 4000, checked191⟩,
  ⟨192, c192, 4000, checked192⟩,
  ⟨193, c193, 4000, checked193⟩,
  ⟨194, c194, 4000, checked194⟩,
  ⟨195, c195, 4000, checked195⟩,
  ⟨196, c196, 4000, checked196⟩,
  ⟨197, c197, 4000, checked197⟩]

end PA215.ContractShards.Shard001Part3
