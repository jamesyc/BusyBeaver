module
public import ZF192.Machine.Decoder.SourceData
public import Mathlib.Data.Nat.Bits

@[expose] public section
namespace M192.Paths
open RegisterMachine.Source

def siteCount : Nat := 3689

def entry (i : Nat) : Entry := (pages.getD (i / 64) []).getD (i % 64) (0, none)

def fpath (i : Nat) : List Bool := (entry i).1.bits.dropLast

def program (i : Nat) : Option Instruction := (entry i).2

end M192.Paths
