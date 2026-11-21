module
public import I3_380.Arithmetic.StandardRun
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem clock_cast (m : Machine) (n c : Nat) :
    clock m.workingStates m.packedRows (n : M) (c : M) =
      ((clock (M := Nat) m.workingStates m.packedRows n c : Nat) : M) :=
  binary_value_cast (clockBlueprint m.workingStates m.packedRows).resultDef
    (clock m.workingStates m.packedRows) (clock m.workingStates m.packedRows)
    (fun _ _ => (clock_eval _ _ _ _ _).mpr rfl)
    (clock_eval _ _) n c

theorem replay_of_run (m : Machine) {n : Nat} {start stop : Configuration}
    (runTo : run m n start = some stop) :
    clock m.workingStates m.packedRows (n : M) (encodeLiteral start : M) = (encodeLiteral stop : M) := by
  rw [clock_cast,clock_nat,totalRun_of_run _ runTo]

end PalomarI3380.ArithmeticMachine
