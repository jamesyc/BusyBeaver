module
public import I3_380.Engine.Arithmetic.RegisterDecrement
public import I3_380.Engine.Arithmetic.StandardTape
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine

open ArithmeticMachine.Reference (positive_of_arithmetic encode_atRight encode_atLeft
  pack_registers pack_registers_nil pack_replicate pack_replicate_nil)
open ArithmeticMachine (packWord packWord_cons packWord_nil)

theorem registers_with_end (vs : List Nat) : registers vs ++ [false] = false :: reverseRegisters vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [registers_cons, reverseRegisters_cons, List.cons_append, List.append_assoc, ih]

/-- Decrement a positive register. The one-cell shift increases the gap. -/
theorem decrement_positive (l : List Bool) (gap a : Nat) (as : List Nat) (v : Nat) (cs : List Nat) :
    atRight Port.dec l (false :: (zeros gap ++ (registers (a :: as) ++
      false :: false :: (ones (v + 2) ++ registers cs))))
      ⟶+ atLeft (Port.breakPort false) l
        (false :: (zeros (gap + 1) ++ registers ((a :: as) ++ v :: cs))) := by
  apply positive_of_arithmetic _ (by change (Port.breakPort false) < 394; decide)
    (by change Port.dec ≠ (Port.breakPort false); decide)
  simpa only [encode_atRight,encode_atLeft,packWord_cons,pack_replicate,pack_replicate_nil,pack_registers,pack_registers_nil,packWord_nil,ArithmeticMachine.ofNat_nat] using
    ArithmeticMachine.Reference.decrementPositive (packWord l (0 : Nat)) gap a as v cs

/-- A zero register incurs the same one-cell shift, with control returned
through the second break port. -/
theorem decrement_zero (l : List Bool) (gap a : Nat) (as cs : List Nat) :
    atRight Port.dec l (false :: (zeros gap ++ (registers (a :: as) ++
      false :: false :: true :: registers cs)))
      ⟶+ atLeft (Port.breakPort true) l
        (false :: (zeros (gap + 1) ++ registers ((a :: as) ++ 0 :: cs))) := by
  apply positive_of_arithmetic _ (by change (Port.breakPort true) < 394; decide)
    (by change Port.dec ≠ (Port.breakPort true); decide)
  simpa only [encode_atRight,encode_atLeft,packWord_cons,pack_replicate,pack_replicate_nil,pack_registers,pack_registers_nil,packWord_nil,ArithmeticMachine.ofNat_nat] using
    ArithmeticMachine.Reference.decrementZero (packWord l (0 : Nat)) gap a as cs

end PalomarI3380.Engine
