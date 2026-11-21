module
public import I3_380.Engine.Selection
public import I3_380.Engine.Decrement
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine

theorem append_zeros (a b : Nat) (tail : List Bool) :
    zeros a ++ (zeros b ++ tail) = zeros (a + b) ++ tail := by
  rw [← List.append_assoc, List.replicate_append_replicate]

/-- Erasing the selector marks restores them to the gap, and the actual
break code updates the instruction pointer. -/
theorem restore_from_register (path : List Bool) (hShort : shortZeros 0 path.reverse = true)
    (skip : Bool) (marks gap : Nat) (rs : List Nat) :
    atLeft (Port.breakPort skip) ((ones marks ++ path.reverse) ++ [true])
        (zeros gap ++ registers rs)
      ⟶+ frame (breakPath skip path.reverse).reverse
        (gap + marks + breakPadding skip path.reverse) rs := by
  have h : shortZeros 0 (ones marks ++ path.reverse) = true := by
    rw [shortZeros_ones]
    exact hShort
  have hr := break_run skip (ones marks ++ path.reverse) h (zeros gap ++ registers rs)
  cases skip with
  | false =>
    have hCount : marks + (breakPadding false path.reverse + gap) =
        gap + marks + breakPadding false path.reverse := by omega
    simpa only [breakPath, Bool.false_eq_true, ↓reduceIte, increment_after_marks,
      List.reverse_append, reverse_zeros, break_padding_after_marks, Nat.add_zero, frame,
      List.append_assoc, append_zeros, hCount] using hr
  | true =>
    have hCount : breakPadding true path.reverse + marks + gap =
        gap + marks + breakPadding true path.reverse := by omega
    simpa only [breakPath, ↓reduceIte, strip_after_marks, break_padding_after_marks,
      frame, append_zeros, hCount] using hr

private theorem decrement_input (v gap : Nat) (before after : List Nat) (l : List Bool) :
    atRight Port.dec l (zeros (gap + 2) ++
      (registers before ++ false :: false :: reverseRegisters (v :: after))) =
    atRight Port.dec l (false :: (zeros (gap + 1) ++
      (registers before ++ false :: false :: (ones (v + 1) ++ registers after)))) := by
  let tape := false :: (zeros (gap + 1) ++
    (registers before ++ false :: false :: (ones (v + 1) ++ registers after)))
  change _ = atRight Port.dec l tape
  rw [← atRight_pad Port.dec l tape 1]
  simp only [tape, show zeros 1 = [false] by rfl, List.cons_append, List.append_assoc,
    registers_with_end, reverseRegisters_cons, List.replicate_succ]

private theorem execute_marked_register (dec : Bool) (v gap a : Nat)
    (as after : List Nat) (l : List Bool) :
    atRight (Port.registerOp dec) l (zeros (gap + 2) ++
      (registers (a :: as) ++ false :: false :: reverseRegisters (v :: after)))
      ⟶+ atLeft (Port.breakPort (zeroDecrement dec v)) l
        (zeros (gap + 2 + bit dec) ++ registers ((a :: as) ++ registerValue dec v :: after)) := by
  cases dec with
  | false =>
    have hPad : registers ((a :: as) ++ (v + 1) :: after) ++ [false] =
        registers (a :: as) ++ false :: (ones (v + 2) ++ false :: reverseRegisters after) := by
      rw [registers_append, List.append_assoc]
      change registers (a :: as) ++
        ((false :: ones (v + 2) ++ registers after) ++ [false]) = _
      simp only [List.cons_append, List.append_assoc, registers_with_end]
    have hRun := increment l gap a as v (false :: reverseRegisters after)
    change _ ⟶+ atLeft (Port.breakPort false) l
      (zeros (gap + 2) ++ registers ((a :: as) ++ (v + 1) :: after))
    rw [← atLeft_pad _ _ _ 1, List.append_assoc, show zeros 1 = [false] by rfl, hPad]
    simpa only [Port.registerOp, Bool.false_eq_true, ↓reduceIte, reverseRegisters_cons, List.replicate_succ,
      List.cons_append, List.append_assoc] using hRun
  | true =>
    rw [show Port.registerOp true = Port.dec by rfl, decrement_input]
    cases v with
    | zero => exact decrement_zero l (gap + 1) a as after
    | succ v =>
      change _ ⟶+ atLeft (Port.breakPort false) l
        (zeros (gap + 3) ++ registers ((a :: as) ++ v :: after))
      exact decrement_positive l (gap + 1) a as v after

/-- A full increment or conditional decrement cycle, through selection,
the arithmetic operation, and the return to the decoder. -/
theorem register_cycle {path : List Bool} {dec : Bool} {r : Fin 12}
    (route : RegisterRoute path dec r) (gap a v : Nat) (as after : List Nat)
    (hIndex : after.length = r.val) :
    frame path (gap + 2 + (r.val + 1)) ((a :: as) ++ v :: after) ⟶+
      frame (breakPath (zeroDecrement dec v) path.reverse).reverse
        (gap + 2 + bit dec + (r.val + 1) + breakPadding (zeroDecrement dec v) path.reverse)
        ((a :: as) ++ registerValue dec v :: after) := by
  let marks := r.val + 1
  let l := ones marks ++ (path.reverse ++ [true])
  let tape := zeros (gap + 2) ++ (registers (a :: as) ++ false :: false :: reverseRegisters (v :: after))
  calc
    _ ⟶* marked path marks (gap + 2) (a :: as) (v :: after) :=
      select_register route _ (by omega) _ _ _ hIndex
    _ ⟶+ atRight (Port.registerEntry dec r.val) (path.reverse ++ [true]) (ones marks ++ tape) :=
      route.run _
    _ ⟶+ atRight (Port.registerOp dec) l tape :=
      enter_operation dec r.val r.isLt _ _
    _ ⟶+ atLeft (Port.breakPort (zeroDecrement dec v)) l
        (zeros (gap + 2 + bit dec) ++ registers ((a :: as) ++ registerValue dec v :: after)) :=
      execute_marked_register dec v gap a as after _
    _ ⟶+ _ := by
      simpa only [l, List.append_assoc] using restore_from_register path route.short
        (zeroDecrement dec v) marks (gap + 2 + bit dec) ((a :: as) ++ registerValue dec v :: after)

end PalomarI3380.Engine
