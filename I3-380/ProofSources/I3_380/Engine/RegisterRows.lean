module
public import I3_380.Engine.Tape
@[expose] public section

namespace PalomarI3380.Engine

namespace Port

abbrev select := 22
abbrev selectGap := 36
abbrev selectScan := 55
abbrev selectSeparator := 73
abbrev selectEnd := 90
abbrev selectBack := 102
abbrev inc := 42
abbrev incGap := 61
abbrev incScan := 79
abbrev incSeparator := 95

abbrev ret (zero : Bool) : Nat := if zero then 76 else 37
abbrev retSeparator (zero : Bool) : Nat := if zero then 92 else 56
abbrev retGap (zero : Bool) : Nat := if zero then 104 else 74
abbrev breakPort (zero : Bool) : Nat := if zero then 15 else 24

abbrev dec := 38
abbrev decGap := 57
abbrev decScan := 75
abbrev decSeparator := 91
abbrev decShift := 103
abbrev decPrevious := 58
abbrev decRewrite := 77
abbrev decSuffix := 93

end Port

theorem return_first (zero : Bool) : Row (Port.ret zero) false false false (Port.retSeparator zero) := by
  cases zero <;> decide +kernel

theorem return_ones (zero : Bool) : Row (Port.ret zero) true true false (Port.ret zero) := by
  cases zero <;> decide +kernel

theorem return_next (zero : Bool) : Row (Port.retSeparator zero) true true false (Port.ret zero) := by
  cases zero <;> decide +kernel

theorem return_enter_gap (zero : Bool) : Row (Port.retSeparator zero) false false false (Port.retGap zero) := by
  cases zero <;> decide +kernel

theorem return_zeros (zero : Bool) : Row (Port.retGap zero) false false false (Port.retGap zero) := by
  cases zero <;> decide +kernel

theorem return_marker (zero : Bool) : Row (Port.retGap zero) true false false (Port.breakPort zero) := by
  cases zero <;> decide +kernel

end PalomarI3380.Engine
