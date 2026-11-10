import PA215.CertifiedContracts
import PA215.Census.C001
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard001Part4
open PA215.Contracts PA215.Census

def original198 : RawOriginal := C001.records[70]'(by decide)
theorem original_id198 : original198.index = 198 := by decide

def c198 : Contract := original198.toContract.get (by decide)
theorem binding198 : original198.toContract = some c198 := rfl

theorem checked198 : check 4000 c198 = true := by decide

def original199 : RawOriginal := C001.records[71]'(by decide)
theorem original_id199 : original199.index = 199 := by decide

def c199 : Contract := original199.toContract.get (by decide)
theorem binding199 : original199.toContract = some c199 := rfl

theorem checked199 : check 4000 c199 = true := by decide

def original200 : RawOriginal := C001.records[72]'(by decide)
theorem original_id200 : original200.index = 200 := by decide

def c200 : Contract := original200.toContract.get (by decide)
theorem binding200 : original200.toContract = some c200 := rfl

theorem checked200 : check 4000 c200 = true := by decide

def original201 : RawOriginal := C001.records[73]'(by decide)
theorem original_id201 : original201.index = 201 := by decide

def c201 : Contract := original201.toContract.get (by decide)
theorem binding201 : original201.toContract = some c201 := rfl

theorem checked201 : check 4000 c201 = true := by decide

def original202 : RawOriginal := C001.records[74]'(by decide)
theorem original_id202 : original202.index = 202 := by decide

def c202 : Contract := original202.toContract.get (by decide)
theorem binding202 : original202.toContract = some c202 := rfl

theorem checked202 : check 4000 c202 = true := by decide

def original203 : RawOriginal := C001.records[75]'(by decide)
theorem original_id203 : original203.index = 203 := by decide

def c203 : Contract := original203.toContract.get (by decide)
theorem binding203 : original203.toContract = some c203 := rfl

theorem checked203 : check 4000 c203 = true := by decide

def original204 : RawOriginal := C001.records[76]'(by decide)
theorem original_id204 : original204.index = 204 := by decide

def c204 : Contract := original204.toContract.get (by decide)
theorem binding204 : original204.toContract = some c204 := rfl

theorem checked204 : check 4000 c204 = true := by decide

def original205 : RawOriginal := C001.records[77]'(by decide)
theorem original_id205 : original205.index = 205 := by decide

def c205 : Contract := original205.toContract.get (by decide)
theorem binding205 : original205.toContract = some c205 := rfl

theorem checked205 : check 4000 c205 = true := by decide

def original206 : RawOriginal := C001.records[78]'(by decide)
theorem original_id206 : original206.index = 206 := by decide

def c206 : Contract := original206.toContract.get (by decide)
theorem binding206 : original206.toContract = some c206 := rfl

theorem checked206 : check 4000 c206 = true := by decide

def original207 : RawOriginal := C001.records[79]'(by decide)
theorem original_id207 : original207.index = 207 := by decide

def c207 : Contract := original207.toContract.get (by decide)
theorem binding207 : original207.toContract = some c207 := rfl

theorem checked207 : check 4000 c207 = true := by decide

def original208 : RawOriginal := C001.records[80]'(by decide)
theorem original_id208 : original208.index = 208 := by decide

def c208 : Contract := original208.toContract.get (by decide)
theorem binding208 : original208.toContract = some c208 := rfl

theorem checked208 : check 4000 c208 = true := by decide

def original209 : RawOriginal := C001.records[81]'(by decide)
theorem original_id209 : original209.index = 209 := by decide

def c209 : Contract := original209.toContract.get (by decide)
theorem binding209 : original209.toContract = some c209 := rfl

theorem checked209 : check 4000 c209 = true := by decide

def original210 : RawOriginal := C001.records[82]'(by decide)
theorem original_id210 : original210.index = 210 := by decide

def c210 : Contract := original210.toContract.get (by decide)
theorem binding210 : original210.toContract = some c210 := rfl

theorem checked210 : check 4000 c210 = true := by decide

def original211 : RawOriginal := C001.records[83]'(by decide)
theorem original_id211 : original211.index = 211 := by decide

def c211 : Contract := original211.toContract.get (by decide)
theorem binding211 : original211.toContract = some c211 := rfl

theorem checked211 : check 4000 c211 = true := by decide

def original212 : RawOriginal := C001.records[84]'(by decide)
theorem original_id212 : original212.index = 212 := by decide

def c212 : Contract := original212.toContract.get (by decide)
theorem binding212 : original212.toContract = some c212 := rfl

theorem checked212 : check 4000 c212 = true := by decide

def original213 : RawOriginal := C001.records[85]'(by decide)
theorem original_id213 : original213.index = 213 := by decide

def c213 : Contract := original213.toContract.get (by decide)
theorem binding213 : original213.toContract = some c213 := rfl

theorem checked213 : check 4000 c213 = true := by decide

def records : List Certified := [
  ⟨198, c198, 4000, checked198⟩,
  ⟨199, c199, 4000, checked199⟩,
  ⟨200, c200, 4000, checked200⟩,
  ⟨201, c201, 4000, checked201⟩,
  ⟨202, c202, 4000, checked202⟩,
  ⟨203, c203, 4000, checked203⟩,
  ⟨204, c204, 4000, checked204⟩,
  ⟨205, c205, 4000, checked205⟩,
  ⟨206, c206, 4000, checked206⟩,
  ⟨207, c207, 4000, checked207⟩,
  ⟨208, c208, 4000, checked208⟩,
  ⟨209, c209, 4000, checked209⟩,
  ⟨210, c210, 4000, checked210⟩,
  ⟨211, c211, 4000, checked211⟩,
  ⟨212, c212, 4000, checked212⟩,
  ⟨213, c213, 4000, checked213⟩]

end PA215.ContractShards.Shard001Part4
