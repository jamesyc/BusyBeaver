import PA215.CertifiedContracts
import PA215.Census.C004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard004Part5
open PA215.Contracts PA215.Census

def original598 : RawOriginal := C004.records[86]'(by decide)
theorem original_id598 : original598.index = 598 := by decide

def c598 : Contract := original598.toContract.get (by decide)
theorem binding598 : original598.toContract = some c598 := rfl

theorem checked598 : check 4000 c598 = true := by decide

def original599 : RawOriginal := C004.records[87]'(by decide)
theorem original_id599 : original599.index = 599 := by decide

def c599 : Contract := original599.toContract.get (by decide)
theorem binding599 : original599.toContract = some c599 := rfl

theorem checked599 : check 4000 c599 = true := by decide

def original600 : RawOriginal := C004.records[88]'(by decide)
theorem original_id600 : original600.index = 600 := by decide

def c600 : Contract := original600.toContract.get (by decide)
theorem binding600 : original600.toContract = some c600 := rfl

theorem checked600 : check 4000 c600 = true := by decide

def original601 : RawOriginal := C004.records[89]'(by decide)
theorem original_id601 : original601.index = 601 := by decide

def c601 : Contract := original601.toContract.get (by decide)
theorem binding601 : original601.toContract = some c601 := rfl

theorem checked601 : check 4000 c601 = true := by decide

def original602 : RawOriginal := C004.records[90]'(by decide)
theorem original_id602 : original602.index = 602 := by decide

def c602 : Contract := original602.toContract.get (by decide)
theorem binding602 : original602.toContract = some c602 := rfl

theorem checked602 : check 4000 c602 = true := by decide

def original603 : RawOriginal := C004.records[91]'(by decide)
theorem original_id603 : original603.index = 603 := by decide

def c603 : Contract := original603.toContract.get (by decide)
theorem binding603 : original603.toContract = some c603 := rfl

theorem checked603 : check 4000 c603 = true := by decide

def original604 : RawOriginal := C004.records[92]'(by decide)
theorem original_id604 : original604.index = 604 := by decide

def c604 : Contract := original604.toContract.get (by decide)
theorem binding604 : original604.toContract = some c604 := rfl

theorem checked604 : check 4000 c604 = true := by decide

def original605 : RawOriginal := C004.records[93]'(by decide)
theorem original_id605 : original605.index = 605 := by decide

def c605 : Contract := original605.toContract.get (by decide)
theorem binding605 : original605.toContract = some c605 := rfl

theorem checked605 : check 4000 c605 = true := by decide

def original606 : RawOriginal := C004.records[94]'(by decide)
theorem original_id606 : original606.index = 606 := by decide

def c606 : Contract := original606.toContract.get (by decide)
theorem binding606 : original606.toContract = some c606 := rfl

theorem checked606 : check 4000 c606 = true := by decide

def original607 : RawOriginal := C004.records[95]'(by decide)
theorem original_id607 : original607.index = 607 := by decide

def c607 : Contract := original607.toContract.get (by decide)
theorem binding607 : original607.toContract = some c607 := rfl

theorem checked607 : check 4000 c607 = true := by decide

def original608 : RawOriginal := C004.records[96]'(by decide)
theorem original_id608 : original608.index = 608 := by decide

def c608 : Contract := original608.toContract.get (by decide)
theorem binding608 : original608.toContract = some c608 := rfl

theorem checked608 : check 4000 c608 = true := by decide

def original609 : RawOriginal := C004.records[97]'(by decide)
theorem original_id609 : original609.index = 609 := by decide

def c609 : Contract := original609.toContract.get (by decide)
theorem binding609 : original609.toContract = some c609 := rfl

theorem checked609 : check 4000 c609 = true := by decide

def original610 : RawOriginal := C004.records[98]'(by decide)
theorem original_id610 : original610.index = 610 := by decide

def c610 : Contract := original610.toContract.get (by decide)
theorem binding610 : original610.toContract = some c610 := rfl

theorem checked610 : check 4000 c610 = true := by decide

def original611 : RawOriginal := C004.records[99]'(by decide)
theorem original_id611 : original611.index = 611 := by decide

def c611 : Contract := original611.toContract.get (by decide)
theorem binding611 : original611.toContract = some c611 := rfl

theorem checked611 : check 4000 c611 = true := by decide

def original612 : RawOriginal := C004.records[100]'(by decide)
theorem original_id612 : original612.index = 612 := by decide

def c612 : Contract := original612.toContract.get (by decide)
theorem binding612 : original612.toContract = some c612 := rfl

theorem checked612 : check 4000 c612 = true := by decide

def original613 : RawOriginal := C004.records[101]'(by decide)
theorem original_id613 : original613.index = 613 := by decide

def c613 : Contract := original613.toContract.get (by decide)
theorem binding613 : original613.toContract = some c613 := rfl

theorem checked613 : check 4000 c613 = true := by decide

def records : List Certified := [
  ⟨598, c598, 4000, checked598⟩,
  ⟨599, c599, 4000, checked599⟩,
  ⟨600, c600, 4000, checked600⟩,
  ⟨601, c601, 4000, checked601⟩,
  ⟨602, c602, 4000, checked602⟩,
  ⟨603, c603, 4000, checked603⟩,
  ⟨604, c604, 4000, checked604⟩,
  ⟨605, c605, 4000, checked605⟩,
  ⟨606, c606, 4000, checked606⟩,
  ⟨607, c607, 4000, checked607⟩,
  ⟨608, c608, 4000, checked608⟩,
  ⟨609, c609, 4000, checked609⟩,
  ⟨610, c610, 4000, checked610⟩,
  ⟨611, c611, 4000, checked611⟩,
  ⟨612, c612, 4000, checked612⟩,
  ⟨613, c613, 4000, checked613⟩]

end PA215.ContractShards.Shard004Part5
