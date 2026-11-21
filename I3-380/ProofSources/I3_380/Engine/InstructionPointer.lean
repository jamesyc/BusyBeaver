module
public import I3_380.Engine.Arithmetic.ControlReturns
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine

open ArithmeticMachine (packWord packWord_append packWord_cons packWord_nil pushBit)
open ArithmeticMachine.Reference (positive_of_arithmetic encode_atRight encode_atLeft pack_replicate_nil)

private theorem marker : packWord [true] (0 : Nat) = 1 := by simp [pushBit]

private theorem dispatch_not_root : ∀ seen : Fin 7, Port.dispatch seen.val ≠ Port.root := by decide

theorem dispatch_from (path : List Bool) (seen : Nat) (hle : seen ≤ 6)
    (h : shortZeros seen path = true) (y : List Bool) :
    atLeft (Port.dispatch seen) (path ++ [true]) y
      ⟶+ atRight Port.root [true] (path.reverse ++ y) := by
  apply positive_of_arithmetic _ (by change Port.root < 394; decide)
    (dispatch_not_root ⟨seen,by omega⟩)
  simpa only [encode_atLeft,encode_atRight,packWord_append,marker] using
    ArithmeticMachine.Reference.dispatchFrom path seen hle h (packWord y (0 : Nat))

/-- Strip a zero when requested, then increment the reversed path and
return to the decoder root. The removed cells become zero padding. -/
theorem break_run (skipZero : Bool) (path : List Bool) (h : shortZeros 0 path = true) (y : List Bool) :
    atLeft (Port.breakPort skipZero) (path ++ [true]) y
      ⟶+ atRight Port.root [true] ((breakPath skipZero path).reverse ++
        (zeros (breakPadding skipZero path) ++ y)) := by
  apply positive_of_arithmetic _ (by change Port.root < 394; decide) (by
    change Port.breakPort skipZero ≠ Port.root
    cases skipZero <;> decide)
  simpa only [encode_atLeft,encode_atRight,pack_replicate_nil,packWord_append,marker,
    FFL.FirstOrder.Arithmetic.natCast_nat] using
    ArithmeticMachine.Reference.breakRun skipZero path h (packWord y (0 : Nat))

/-- Erase up to and including the first one, then resume decoding. -/
theorem continue_one (path : List Bool) (h : shortZeros 0 path = true) (hasOne : true ∈ path)
    (y : List Bool) :
    atLeft Port.continueOne (path ++ [true]) y
      ⟶+ atRight Port.root [true] ((stripThrough true path).reverse ++
        (zeros (path.length - (stripThrough true path).length) ++ y)) := by
  apply positive_of_arithmetic _ (by change Port.root < 394; decide)
    (by change Port.continueOne ≠ Port.root; decide)
  simpa only [encode_atLeft,encode_atRight,pack_replicate_nil,packWord_append,marker,
    FFL.FirstOrder.Arithmetic.natCast_nat] using
    ArithmeticMachine.Reference.continueOne path h hasOne (packWord y (0 : Nat))

end PalomarI3380.Engine
