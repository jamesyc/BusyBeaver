import PA215.CertifiedContracts
import PA215.Census.C001
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard001Part2
open PA215.Contracts PA215.Census

def original166 : RawOriginal := C001.records[38]'(by decide)
theorem original_id166 : original166.index = 166 := by decide

def c166 : Contract := original166.toContract.get (by decide)
theorem binding166 : original166.toContract = some c166 := rfl

theorem checked166 : check 4000 c166 = true := by decide

def original167 : RawOriginal := C001.records[39]'(by decide)
theorem original_id167 : original167.index = 167 := by decide

def c167 : Contract := original167.toContract.get (by decide)
theorem binding167 : original167.toContract = some c167 := rfl

theorem checked167 : check 4000 c167 = true := by decide

def original168 : RawOriginal := C001.records[40]'(by decide)
theorem original_id168 : original168.index = 168 := by decide

def c168 : Contract := original168.toContract.get (by decide)
theorem binding168 : original168.toContract = some c168 := rfl

theorem checked168 : check 4000 c168 = true := by decide

def original169 : RawOriginal := C001.records[41]'(by decide)
theorem original_id169 : original169.index = 169 := by decide

def c169 : Contract := original169.toContract.get (by decide)
theorem binding169 : original169.toContract = some c169 := rfl

theorem checked169 : check 4000 c169 = true := by decide

def original170 : RawOriginal := C001.records[42]'(by decide)
theorem original_id170 : original170.index = 170 := by decide

def c170 : Contract := original170.toContract.get (by decide)
theorem binding170 : original170.toContract = some c170 := rfl

theorem checked170 : check 4000 c170 = true := by decide

def original171 : RawOriginal := C001.records[43]'(by decide)
theorem original_id171 : original171.index = 171 := by decide

def c171 : Contract := original171.toContract.get (by decide)
theorem binding171 : original171.toContract = some c171 := rfl

theorem checked171 : check 4000 c171 = true := by decide

def original172 : RawOriginal := C001.records[44]'(by decide)
theorem original_id172 : original172.index = 172 := by decide

def c172 : Contract := original172.toContract.get (by decide)
theorem binding172 : original172.toContract = some c172 := rfl

theorem checked172 : check 4000 c172 = true := by decide

def original173 : RawOriginal := C001.records[45]'(by decide)
theorem original_id173 : original173.index = 173 := by decide

def c173 : Contract := original173.toContract.get (by decide)
theorem binding173 : original173.toContract = some c173 := rfl

theorem checked173 : check 4000 c173 = true := by decide

def original174 : RawOriginal := C001.records[46]'(by decide)
theorem original_id174 : original174.index = 174 := by decide

def c174 : Contract := original174.toContract.get (by decide)
theorem binding174 : original174.toContract = some c174 := rfl

theorem checked174 : check 4000 c174 = true := by decide

def original175 : RawOriginal := C001.records[47]'(by decide)
theorem original_id175 : original175.index = 175 := by decide

def c175 : Contract := original175.toContract.get (by decide)
theorem binding175 : original175.toContract = some c175 := rfl

theorem checked175 : check 4000 c175 = true := by decide

def original176 : RawOriginal := C001.records[48]'(by decide)
theorem original_id176 : original176.index = 176 := by decide

def c176 : Contract := original176.toContract.get (by decide)
theorem binding176 : original176.toContract = some c176 := rfl

theorem checked176 : check 4000 c176 = true := by decide

def original177 : RawOriginal := C001.records[49]'(by decide)
theorem original_id177 : original177.index = 177 := by decide

def c177 : Contract := original177.toContract.get (by decide)
theorem binding177 : original177.toContract = some c177 := rfl

theorem checked177 : check 4000 c177 = true := by decide

def original178 : RawOriginal := C001.records[50]'(by decide)
theorem original_id178 : original178.index = 178 := by decide

def c178 : Contract := original178.toContract.get (by decide)
theorem binding178 : original178.toContract = some c178 := rfl

theorem checked178 : check 4000 c178 = true := by decide

def original179 : RawOriginal := C001.records[51]'(by decide)
theorem original_id179 : original179.index = 179 := by decide

def c179 : Contract := original179.toContract.get (by decide)
theorem binding179 : original179.toContract = some c179 := rfl

theorem checked179 : check 4000 c179 = true := by decide

def original180 : RawOriginal := C001.records[52]'(by decide)
theorem original_id180 : original180.index = 180 := by decide

def c180 : Contract := original180.toContract.get (by decide)
theorem binding180 : original180.toContract = some c180 := rfl

theorem checked180 : check 4000 c180 = true := by decide

def original181 : RawOriginal := C001.records[53]'(by decide)
theorem original_id181 : original181.index = 181 := by decide

def c181 : Contract := original181.toContract.get (by decide)
theorem binding181 : original181.toContract = some c181 := rfl

theorem checked181 : check 4000 c181 = true := by decide

def records : List Certified := [
  ⟨166, c166, 4000, checked166⟩,
  ⟨167, c167, 4000, checked167⟩,
  ⟨168, c168, 4000, checked168⟩,
  ⟨169, c169, 4000, checked169⟩,
  ⟨170, c170, 4000, checked170⟩,
  ⟨171, c171, 4000, checked171⟩,
  ⟨172, c172, 4000, checked172⟩,
  ⟨173, c173, 4000, checked173⟩,
  ⟨174, c174, 4000, checked174⟩,
  ⟨175, c175, 4000, checked175⟩,
  ⟨176, c176, 4000, checked176⟩,
  ⟨177, c177, 4000, checked177⟩,
  ⟨178, c178, 4000, checked178⟩,
  ⟨179, c179, 4000, checked179⟩,
  ⟨180, c180, 4000, checked180⟩,
  ⟨181, c181, 4000, checked181⟩]

end PA215.ContractShards.Shard001Part2
