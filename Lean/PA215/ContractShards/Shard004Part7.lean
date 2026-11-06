import PA215.CertifiedContracts
import PA215.Census.C004
import PA215.Census.C005
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard004Part7
open PA215.Contracts PA215.Census

def original630 : RawOriginal := C004.records[118]'(by decide)
theorem original_id630 : original630.index = 630 := by decide

def c630 : Contract := original630.toContract.get (by decide)
theorem binding630 : original630.toContract = some c630 := rfl

theorem checked630 : check 4000 c630 = true := by decide

def original631 : RawOriginal := C004.records[119]'(by decide)
theorem original_id631 : original631.index = 631 := by decide

def c631 : Contract := original631.toContract.get (by decide)
theorem binding631 : original631.toContract = some c631 := rfl

theorem checked631 : check 4000 c631 = true := by decide

def original632 : RawOriginal := C004.records[120]'(by decide)
theorem original_id632 : original632.index = 632 := by decide

def c632 : Contract := original632.toContract.get (by decide)
theorem binding632 : original632.toContract = some c632 := rfl

theorem checked632 : check 4000 c632 = true := by decide

def original633 : RawOriginal := C004.records[121]'(by decide)
theorem original_id633 : original633.index = 633 := by decide

def c633 : Contract := original633.toContract.get (by decide)
theorem binding633 : original633.toContract = some c633 := rfl

theorem checked633 : check 4000 c633 = true := by decide

def original634 : RawOriginal := C004.records[122]'(by decide)
theorem original_id634 : original634.index = 634 := by decide

def c634 : Contract := original634.toContract.get (by decide)
theorem binding634 : original634.toContract = some c634 := rfl

theorem checked634 : check 4000 c634 = true := by decide

def original635 : RawOriginal := C004.records[123]'(by decide)
theorem original_id635 : original635.index = 635 := by decide

def c635 : Contract := original635.toContract.get (by decide)
theorem binding635 : original635.toContract = some c635 := rfl

theorem checked635 : check 4000 c635 = true := by decide

def original636 : RawOriginal := C004.records[124]'(by decide)
theorem original_id636 : original636.index = 636 := by decide

def c636 : Contract := original636.toContract.get (by decide)
theorem binding636 : original636.toContract = some c636 := rfl

theorem checked636 : check 4000 c636 = true := by decide

def original637 : RawOriginal := C004.records[125]'(by decide)
theorem original_id637 : original637.index = 637 := by decide

def c637 : Contract := original637.toContract.get (by decide)
theorem binding637 : original637.toContract = some c637 := rfl

theorem checked637 : check 4000 c637 = true := by decide

def original638 : RawOriginal := C004.records[126]'(by decide)
theorem original_id638 : original638.index = 638 := by decide

def c638 : Contract := original638.toContract.get (by decide)
theorem binding638 : original638.toContract = some c638 := rfl

theorem checked638 : check 4000 c638 = true := by decide

def original639 : RawOriginal := C004.records[127]'(by decide)
theorem original_id639 : original639.index = 639 := by decide

def c639 : Contract := original639.toContract.get (by decide)
theorem binding639 : original639.toContract = some c639 := rfl

theorem checked639 : check 4000 c639 = true := by decide

def original640 : RawOriginal := C005.records[0]'(by decide)
theorem original_id640 : original640.index = 640 := by decide

def c640 : Contract := original640.toContract.get (by decide)
theorem binding640 : original640.toContract = some c640 := rfl

theorem checked640 : check 4000 c640 = true := by decide

def original641 : RawOriginal := C005.records[1]'(by decide)
theorem original_id641 : original641.index = 641 := by decide

def c641 : Contract := original641.toContract.get (by decide)
theorem binding641 : original641.toContract = some c641 := rfl

theorem checked641 : check 4000 c641 = true := by decide

def original642 : RawOriginal := C005.records[2]'(by decide)
theorem original_id642 : original642.index = 642 := by decide

def c642 : Contract := original642.toContract.get (by decide)
theorem binding642 : original642.toContract = some c642 := rfl

theorem checked642 : check 4000 c642 = true := by decide

def original643 : RawOriginal := C005.records[3]'(by decide)
theorem original_id643 : original643.index = 643 := by decide

def c643 : Contract := original643.toContract.get (by decide)
theorem binding643 : original643.toContract = some c643 := rfl

theorem checked643 : check 4000 c643 = true := by decide

def original644 : RawOriginal := C005.records[4]'(by decide)
theorem original_id644 : original644.index = 644 := by decide

def c644 : Contract := original644.toContract.get (by decide)
theorem binding644 : original644.toContract = some c644 := rfl

theorem checked644 : check 4000 c644 = true := by decide

def original645 : RawOriginal := C005.records[5]'(by decide)
theorem original_id645 : original645.index = 645 := by decide

def c645 : Contract := original645.toContract.get (by decide)
theorem binding645 : original645.toContract = some c645 := rfl

theorem checked645 : check 4000 c645 = true := by decide

def records : List Certified := [
  ⟨630, c630, 4000, checked630⟩,
  ⟨631, c631, 4000, checked631⟩,
  ⟨632, c632, 4000, checked632⟩,
  ⟨633, c633, 4000, checked633⟩,
  ⟨634, c634, 4000, checked634⟩,
  ⟨635, c635, 4000, checked635⟩,
  ⟨636, c636, 4000, checked636⟩,
  ⟨637, c637, 4000, checked637⟩,
  ⟨638, c638, 4000, checked638⟩,
  ⟨639, c639, 4000, checked639⟩,
  ⟨640, c640, 4000, checked640⟩,
  ⟨641, c641, 4000, checked641⟩,
  ⟨642, c642, 4000, checked642⟩,
  ⟨643, c643, 4000, checked643⟩,
  ⟨644, c644, 4000, checked644⟩,
  ⟨645, c645, 4000, checked645⟩]

end PA215.ContractShards.Shard004Part7
