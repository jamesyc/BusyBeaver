module
public import I3_380.Engine.Arithmetic.RegisterSelection
public import I3_380.Engine.Arithmetic.StandardTape
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine
open ArithmeticMachine.Reference (positive_of_arithmetic encode_atRight encode_atLeft
  pack_registers pack_registers_nil pack_replicate pack_replicate_nil)
open ArithmeticMachine (packWord packWord_cons)

/-- Move the extra separator across the preceding register. -/
theorem select (l : List Bool) (gap : Nat) (as : List Nat) (v : Nat) (x : List Bool) :
    atRight Port.select l (false :: (zeros (gap + 1) ++ (registers (as ++ [v]) ++ false :: false :: x)))
      ⟶+ atLeft (Port.breakPort false) l
        (false :: (zeros (gap + 1) ++ (registers as ++ false :: false :: (ones (v + 1) ++ false :: x)))) := by
  apply positive_of_arithmetic _ (by change (Port.breakPort false) < 394; decide)
    (by change Port.select ≠ (Port.breakPort false); decide)
  simpa only [encode_atRight,encode_atLeft,packWord_cons,pack_replicate,pack_replicate_nil,pack_registers,pack_registers_nil,ArithmeticMachine.ofNat_nat] using
    ArithmeticMachine.Reference.selectRegister (packWord l (0 : Nat)) gap as v (packWord x 0)

/-- Increment the selected register, using the extra separator as a new one. -/
theorem increment (l : List Bool) (gap : Nat) (a : Nat) (as : List Nat) (v : Nat) (x : List Bool) :
    atRight Port.inc l (false :: (zeros (gap + 1) ++
      (registers (a :: as) ++ false :: false :: (ones (v + 1) ++ x))))
      ⟶+ atLeft (Port.breakPort false) l (false :: (zeros (gap + 1) ++
        (registers (a :: as) ++ false :: (ones (v + 2) ++ x)))) := by
  apply positive_of_arithmetic _ (by change (Port.breakPort false) < 394; decide)
    (by change Port.inc ≠ (Port.breakPort false); decide)
  simpa only [encode_atRight,encode_atLeft,packWord_cons,pack_replicate,pack_replicate_nil,pack_registers,pack_registers_nil,ArithmeticMachine.ofNat_nat] using
    ArithmeticMachine.Reference.incrementRegister (packWord l (0 : Nat)) gap a as v (packWord x 0)

end PalomarI3380.Engine
