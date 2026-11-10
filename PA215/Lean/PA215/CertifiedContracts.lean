import PA215.Contracts

namespace PA215.Contracts
open PA215.Zip PA215.Runtime PA215.NativeTable

/-- A registry entry carries its own kernel-checked acceptance proof. -/
structure Certified where
  id : Nat
  data : Contract
  fuel : Nat
  accepted : check fuel data = true

theorem Certified.sound (c : Certified) (n : Nat) (vs : List Nat)
    (hv : Valid c.data.branch vs) :
    Reach1 machine (conc n vs c.data.initial) (conc n vs c.data.target) :=
  Contracts.sound c.fuel c.data c.accepted n vs hv

end PA215.Contracts
