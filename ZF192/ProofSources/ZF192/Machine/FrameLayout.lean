module
public import ZF192.Machine.Decoder.Window
public import ZF192.Machine.Decoder.Paths
public import ZF192.Machine.RegisterProtocol
@[expose] public section
/-! # Source frames as external configurations

At a source boundary the tape of ZF192 is: the program window of the current address, `n`
padding ones, the gate `00`, the nine register blocks `1^(v+1) 0` (source register `r` is
block `r`), and a blank file exterior; right of the window an arbitrary
finite word `ρ`. -/
namespace M192
open M192.Window M192.Paths BinaryTape

def fileN (vs : List Nat) (X : List Bool) : List Bool :=
  vs.foldr (fun v t => List.replicate (v + 1) true ++ false :: t) X
/-- Tape order of the nine registers: block `j` holds register `j`. -/
def regListN (r : Fin 9 → Nat) : List Nat := List.ofFn r
def leftN (r : Fin 9 → Nat) (n : Nat) : List Bool :=
  List.replicate n true ++ false :: false :: fileN (regListN r) []
def frameN (pc : Nat) (r : Fin 9 → Nat) (n : Nat) (ρ : List Bool) : Conf :=
  zc root (winL (fpath pc) ++ leftN r n) (winR (fpath pc) ++ ρ)

end M192
