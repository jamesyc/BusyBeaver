import PA215.CertifiedContracts
import PA215.Census.C002
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard002Part3
open PA215.Contracts PA215.Census

def original310 : RawOriginal := C002.records[54]'(by decide)
theorem original_id310 : original310.index = 310 := by decide

def c310 : Contract := original310.toContract.get (by decide)
theorem binding310 : original310.toContract = some c310 := rfl

theorem checked310 : check 4000 c310 = true := by decide

def original311 : RawOriginal := C002.records[55]'(by decide)
theorem original_id311 : original311.index = 311 := by decide

def c311 : Contract := original311.toContract.get (by decide)
theorem binding311 : original311.toContract = some c311 := rfl

theorem checked311 : check 4000 c311 = true := by decide

def original312 : RawOriginal := C002.records[56]'(by decide)
theorem original_id312 : original312.index = 312 := by decide

def c312 : Contract := original312.toContract.get (by decide)
theorem binding312 : original312.toContract = some c312 := rfl

theorem checked312 : check 4000 c312 = true := by decide

def original313 : RawOriginal := C002.records[57]'(by decide)
theorem original_id313 : original313.index = 313 := by decide

def c313 : Contract := original313.toContract.get (by decide)
theorem binding313 : original313.toContract = some c313 := rfl

theorem checked313 : check 4000 c313 = true := by decide

def original314 : RawOriginal := C002.records[58]'(by decide)
theorem original_id314 : original314.index = 314 := by decide

def c314 : Contract := original314.toContract.get (by decide)
theorem binding314 : original314.toContract = some c314 := rfl

theorem checked314 : check 4000 c314 = true := by decide

def original315 : RawOriginal := C002.records[59]'(by decide)
theorem original_id315 : original315.index = 315 := by decide

def c315 : Contract := original315.toContract.get (by decide)
theorem binding315 : original315.toContract = some c315 := rfl

theorem checked315 : check 4000 c315 = true := by decide

def original316 : RawOriginal := C002.records[60]'(by decide)
theorem original_id316 : original316.index = 316 := by decide

def c316 : Contract := original316.toContract.get (by decide)
theorem binding316 : original316.toContract = some c316 := rfl

theorem checked316 : check 4000 c316 = true := by decide

def original317 : RawOriginal := C002.records[61]'(by decide)
theorem original_id317 : original317.index = 317 := by decide

def c317 : Contract := original317.toContract.get (by decide)
theorem binding317 : original317.toContract = some c317 := rfl

theorem checked317 : check 4000 c317 = true := by decide

def original318 : RawOriginal := C002.records[62]'(by decide)
theorem original_id318 : original318.index = 318 := by decide

def c318 : Contract := original318.toContract.get (by decide)
theorem binding318 : original318.toContract = some c318 := rfl

theorem checked318 : check 4000 c318 = true := by decide

def original319 : RawOriginal := C002.records[63]'(by decide)
theorem original_id319 : original319.index = 319 := by decide

def c319 : Contract := original319.toContract.get (by decide)
theorem binding319 : original319.toContract = some c319 := rfl

theorem checked319 : check 4000 c319 = true := by decide

def original320 : RawOriginal := C002.records[64]'(by decide)
theorem original_id320 : original320.index = 320 := by decide

def c320 : Contract := original320.toContract.get (by decide)
theorem binding320 : original320.toContract = some c320 := rfl

theorem checked320 : check 4000 c320 = true := by decide

def original321 : RawOriginal := C002.records[65]'(by decide)
theorem original_id321 : original321.index = 321 := by decide

def c321 : Contract := original321.toContract.get (by decide)
theorem binding321 : original321.toContract = some c321 := rfl

theorem checked321 : check 4000 c321 = true := by decide

def original322 : RawOriginal := C002.records[66]'(by decide)
theorem original_id322 : original322.index = 322 := by decide

def c322 : Contract := original322.toContract.get (by decide)
theorem binding322 : original322.toContract = some c322 := rfl

theorem checked322 : check 4000 c322 = true := by decide

def original323 : RawOriginal := C002.records[67]'(by decide)
theorem original_id323 : original323.index = 323 := by decide

def c323 : Contract := original323.toContract.get (by decide)
theorem binding323 : original323.toContract = some c323 := rfl

theorem checked323 : check 4000 c323 = true := by decide

def original324 : RawOriginal := C002.records[68]'(by decide)
theorem original_id324 : original324.index = 324 := by decide

def c324 : Contract := original324.toContract.get (by decide)
theorem binding324 : original324.toContract = some c324 := rfl

theorem checked324 : check 4000 c324 = true := by decide

def original325 : RawOriginal := C002.records[69]'(by decide)
theorem original_id325 : original325.index = 325 := by decide

def c325 : Contract := original325.toContract.get (by decide)
theorem binding325 : original325.toContract = some c325 := rfl

theorem checked325 : check 4000 c325 = true := by decide

def records : List Certified := [
  ⟨310, c310, 4000, checked310⟩,
  ⟨311, c311, 4000, checked311⟩,
  ⟨312, c312, 4000, checked312⟩,
  ⟨313, c313, 4000, checked313⟩,
  ⟨314, c314, 4000, checked314⟩,
  ⟨315, c315, 4000, checked315⟩,
  ⟨316, c316, 4000, checked316⟩,
  ⟨317, c317, 4000, checked317⟩,
  ⟨318, c318, 4000, checked318⟩,
  ⟨319, c319, 4000, checked319⟩,
  ⟨320, c320, 4000, checked320⟩,
  ⟨321, c321, 4000, checked321⟩,
  ⟨322, c322, 4000, checked322⟩,
  ⟨323, c323, 4000, checked323⟩,
  ⟨324, c324, 4000, checked324⟩,
  ⟨325, c325, 4000, checked325⟩]

end PA215.ContractShards.Shard002Part3
