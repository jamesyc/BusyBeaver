import PA215.Contracts

namespace PA215.Census
open PA215.Runtime

/-- Exact mathematical input fields from the original5134-obligation census.
    EHalt's absent argument stays none; it is never replaced with an invented0. -/
structure RawOriginal where
  index : Nat
  siteIndex : Nat
  path : List Bool
  tag : String
  arg : Option Nat
  branch : Branch
  initial : SConf
  target : Option SConf
  isHalt : Bool
  deriving DecidableEq, Repr

def RawOriginal.toContract (r : RawOriginal) : Option PA215.Contracts.Contract :=
  r.target.map fun t => ⟨r.branch, r.initial, t⟩

end PA215.Census
