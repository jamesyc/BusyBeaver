import PA215.CertifiedContracts
import PA215.Census.C001
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard001Part0
open PA215.Contracts PA215.Census

def original134 : RawOriginal := C001.records[6]'(by decide)
theorem original_id134 : original134.index = 134 := by decide

def c134 : Contract := original134.toContract.get (by decide)
theorem binding134 : original134.toContract = some c134 := rfl

theorem checked134 : check 4000 c134 = true := by decide

def original135 : RawOriginal := C001.records[7]'(by decide)
theorem original_id135 : original135.index = 135 := by decide

def c135 : Contract := original135.toContract.get (by decide)
theorem binding135 : original135.toContract = some c135 := rfl

theorem checked135 : check 4000 c135 = true := by decide

def original136 : RawOriginal := C001.records[8]'(by decide)
theorem original_id136 : original136.index = 136 := by decide

def c136 : Contract := original136.toContract.get (by decide)
theorem binding136 : original136.toContract = some c136 := rfl

theorem checked136 : check 4000 c136 = true := by decide

def original137 : RawOriginal := C001.records[9]'(by decide)
theorem original_id137 : original137.index = 137 := by decide

def c137 : Contract := original137.toContract.get (by decide)
theorem binding137 : original137.toContract = some c137 := rfl

theorem checked137 : check 4000 c137 = true := by decide

def original138 : RawOriginal := C001.records[10]'(by decide)
theorem original_id138 : original138.index = 138 := by decide

def c138 : Contract := original138.toContract.get (by decide)
theorem binding138 : original138.toContract = some c138 := rfl

theorem checked138 : check 4000 c138 = true := by decide

def original139 : RawOriginal := C001.records[11]'(by decide)
theorem original_id139 : original139.index = 139 := by decide

def c139 : Contract := original139.toContract.get (by decide)
theorem binding139 : original139.toContract = some c139 := rfl

theorem checked139 : check 4000 c139 = true := by decide

def original140 : RawOriginal := C001.records[12]'(by decide)
theorem original_id140 : original140.index = 140 := by decide

def c140 : Contract := original140.toContract.get (by decide)
theorem binding140 : original140.toContract = some c140 := rfl

theorem checked140 : check 4000 c140 = true := by decide

def original141 : RawOriginal := C001.records[13]'(by decide)
theorem original_id141 : original141.index = 141 := by decide

def c141 : Contract := original141.toContract.get (by decide)
theorem binding141 : original141.toContract = some c141 := rfl

theorem checked141 : check 4000 c141 = true := by decide

def original142 : RawOriginal := C001.records[14]'(by decide)
theorem original_id142 : original142.index = 142 := by decide

def c142 : Contract := original142.toContract.get (by decide)
theorem binding142 : original142.toContract = some c142 := rfl

theorem checked142 : check 4000 c142 = true := by decide

def original143 : RawOriginal := C001.records[15]'(by decide)
theorem original_id143 : original143.index = 143 := by decide

def c143 : Contract := original143.toContract.get (by decide)
theorem binding143 : original143.toContract = some c143 := rfl

theorem checked143 : check 4000 c143 = true := by decide

def original144 : RawOriginal := C001.records[16]'(by decide)
theorem original_id144 : original144.index = 144 := by decide

def c144 : Contract := original144.toContract.get (by decide)
theorem binding144 : original144.toContract = some c144 := rfl

theorem checked144 : check 4000 c144 = true := by decide

def original145 : RawOriginal := C001.records[17]'(by decide)
theorem original_id145 : original145.index = 145 := by decide

def c145 : Contract := original145.toContract.get (by decide)
theorem binding145 : original145.toContract = some c145 := rfl

theorem checked145 : check 4000 c145 = true := by decide

def original146 : RawOriginal := C001.records[18]'(by decide)
theorem original_id146 : original146.index = 146 := by decide

def c146 : Contract := original146.toContract.get (by decide)
theorem binding146 : original146.toContract = some c146 := rfl

theorem checked146 : check 4000 c146 = true := by decide

def original147 : RawOriginal := C001.records[19]'(by decide)
theorem original_id147 : original147.index = 147 := by decide

def c147 : Contract := original147.toContract.get (by decide)
theorem binding147 : original147.toContract = some c147 := rfl

theorem checked147 : check 4000 c147 = true := by decide

def original148 : RawOriginal := C001.records[20]'(by decide)
theorem original_id148 : original148.index = 148 := by decide

def c148 : Contract := original148.toContract.get (by decide)
theorem binding148 : original148.toContract = some c148 := rfl

theorem checked148 : check 4000 c148 = true := by decide

def original149 : RawOriginal := C001.records[21]'(by decide)
theorem original_id149 : original149.index = 149 := by decide

def c149 : Contract := original149.toContract.get (by decide)
theorem binding149 : original149.toContract = some c149 := rfl

theorem checked149 : check 4000 c149 = true := by decide

def records : List Certified := [
  ⟨134, c134, 4000, checked134⟩,
  ⟨135, c135, 4000, checked135⟩,
  ⟨136, c136, 4000, checked136⟩,
  ⟨137, c137, 4000, checked137⟩,
  ⟨138, c138, 4000, checked138⟩,
  ⟨139, c139, 4000, checked139⟩,
  ⟨140, c140, 4000, checked140⟩,
  ⟨141, c141, 4000, checked141⟩,
  ⟨142, c142, 4000, checked142⟩,
  ⟨143, c143, 4000, checked143⟩,
  ⟨144, c144, 4000, checked144⟩,
  ⟨145, c145, 4000, checked145⟩,
  ⟨146, c146, 4000, checked146⟩,
  ⟨147, c147, 4000, checked147⟩,
  ⟨148, c148, 4000, checked148⟩,
  ⟨149, c149, 4000, checked149⟩]

end PA215.ContractShards.Shard001Part0
