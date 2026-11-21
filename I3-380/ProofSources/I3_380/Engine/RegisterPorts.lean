module
public import I3_380.Engine.RegisterRows
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine

namespace Port

abbrev root := 7

/-- Entry indices follow the register declaration order
`np, pl, sel, goal, fr, gues, lv, dc, u, tmp, tok, exp`. -/
def registerEntry (decrement : Bool) (r : Nat) : Nat :=
  if decrement then
    #[23, 14, 80, 62, 85, 68, 66, 47, 30, 49, 32, 142][r]?.getD 394
  else
    #[27, 48, 96, 81, 67, 50, 97, 82, 64, 111, 106, 168][r]?.getD 394

def registerOp (decrement : Bool) : Nat := if decrement then dec else inc

end Port

theorem entry_zero : ∀ (dec : Bool) (r : Fin 12),
    Row (Port.registerEntry dec r.val) false false true Port.select := by
  decide +kernel

theorem entry_advance : ∀ (dec : Bool) (r : Fin 11),
    Row (Port.registerEntry dec (r.val + 1)) true true true (Port.registerEntry dec r.val) := by
  decide +kernel

theorem entry_operation : ∀ dec : Bool,
    Row (Port.registerEntry dec 0) true true true (Port.registerOp dec) := by
  decide +kernel

/-- Fewer than `r + 1` marks sends the head to the selector. -/
theorem enter_selector (dec : Bool) (r n : Nat) (hr : r < 12) (hn : n ≤ r) (l x : List Bool) :
    atRight (Port.registerEntry dec r) l (ones n ++ false :: x)
      ⟶+ atRight Port.select (false :: (ones n ++ l)) x := by
  induction n generalizing r l with
  | zero => exact right (entry_zero dec ⟨r, hr⟩) _ _
  | succ n ih =>
    cases r with
    | zero => omega
    | succ r =>
      calc
        _ ⟶+ atRight (Port.registerEntry dec r) (true :: l) (ones n ++ false :: x) :=
          right (entry_advance dec ⟨r, by omega⟩) _ _
        _ ⟶+ _ := by
          simpa only [List.replicate_succ, List.cons_append, repeat_slide] using
            ih r (by omega) (by omega) (true :: l)

/-- Exactly `r + 1` marks select the operation. -/
theorem enter_operation (dec : Bool) (r : Nat) (hr : r < 12) (l x : List Bool) :
    atRight (Port.registerEntry dec r) l (ones (r + 1) ++ x)
      ⟶+ atRight (Port.registerOp dec) (ones (r + 1) ++ l) x := by
  induction r generalizing l with
  | zero => exact right (entry_operation dec) _ _
  | succ r ih =>
    calc
      _ ⟶+ atRight (Port.registerEntry dec r) (true :: l) (ones (r + 1) ++ x) :=
        right (entry_advance dec ⟨r, by omega⟩) _ _
      _ ⟶+ _ := by
        simpa only [List.replicate_succ, List.cons_append, repeat_slide] using
          ih (by omega) (true :: l)

end PalomarI3380.Engine
