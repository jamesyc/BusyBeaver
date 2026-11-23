module
public import I3_334Support.Search.Compiler.Paths
public import I3_334Support.Machine.Simulation
@[expose] public section

namespace PalomarI3380.Compiler

open Engine (incrementReversed stripThrough)

inductive Moves (root : Program) : PathState → PathState → Prop where
  | refl : Moves root s s
  | edge : step root s = some t → Moves root t u → Moves root s u

def Positive (root : Program) (s t : PathState) : Prop :=
  ∃ u, step root s = some u ∧ Moves root u t

theorem Moves.trans {root : Program} {s t u : PathState} (h : Moves root s t) (rest : Moves root t u) :
    Moves root s u := by
  induction h with
  | refl => exact rest
  | edge edge _ ih => exact .edge edge (ih rest)

theorem Positive.trans {root : Program} {s t u : PathState} (h : Positive root s t)
    (rest : Positive root t u) : Positive root s u := by
  obtain ⟨v, edge, mv⟩ := h
  obtain ⟨z, edge', mv'⟩ := rest
  exact ⟨v, edge, mv.trans (.edge edge' mv')⟩

theorem Moves.prepend_halt {root : Program} {s t : PathState} (h : Moves root s t)
    (halt : Terminates (step root) t) : Terminates (step root) s := by
  induction h with
  | refl => exact halt
  | edge edge _ ih => exact .advance edge (ih halt)

private theorem normal_ne_halt : Flow.normal ≠ .halt := by decide
private theorem escape_ne_halt (n : Nat) : Flow.escape n ≠ .halt := by intro h; cases h
private theorem repeatAt_ne_halt (n : Nat) : Flow.repeatAt n ≠ .halt := by intro h; cases h

def LeavesAt (root : Program) (start : PathState) (boundary : List Bool) (flow : Flow) (final : Store) : Prop :=
  if flow = .halt then Terminates (step root) start
  else Positive root start (atPath (destination boundary flow) final)

theorem LeavesAt.prepend {root : Program} {start next : PathState} {boundary : List Bool}
    {flow : Flow} {final : Store} (first : Positive root start next)
    (rest : LeavesAt root next boundary flow final) : LeavesAt root start boundary flow final := by
  cases flow <;> simp only [LeavesAt, normal_ne_halt, escape_ne_halt, repeatAt_ne_halt,
    ↓reduceIte] at rest ⊢
  · exact first.trans rest
  · exact first.trans rest
  · exact first.trans rest
  · obtain ⟨u, eq, path⟩ := first
    exact (Moves.edge eq path).prepend_halt rest

private theorem leave_left {root : Program} {start : PathState} {flow out : Flow} {t : Store}
    (p : List Bool) (hOut : flow.fromLeft = some out)
    (h : LeavesAt root start (p ++ [false]) flow t) : LeavesAt root start p out t := by
  cases flow with
  | normal => simp [Flow.fromLeft] at hOut
  | halt => cases hOut; exact h
  | repeatAt k =>
    cases hOut
    simpa only [LeavesAt, repeatAt_ne_halt, ↓reduceIte, destination, List.reverse_append,
      List.reverse_singleton, List.reverse_nil, List.nil_append, List.singleton_append, stripMany_miss (by decide : false ≠ true)]
      using h
  | escape k =>
    cases k with
    | zero =>
      cases hOut
      simpa only [LeavesAt, escape_ne_halt, normal_ne_halt, ↓reduceIte, destination,
        List.reverse_append, List.reverse_singleton, List.reverse_nil, List.nil_append, List.singleton_append, stripMany_hit, stripMany, stripThrough, ↓reduceIte,
        incrementPath] using h
    | succ n =>
      cases hOut
      simpa only [LeavesAt, escape_ne_halt, ↓reduceIte, destination, List.reverse_append,
        List.reverse_singleton, List.reverse_nil, List.nil_append, List.singleton_append, stripMany_hit] using h

private theorem leave_right {root : Program} {start : PathState} {flow out : Flow} {t : Store}
    (p : List Bool) (hOut : flow.fromRight = some out)
    (h : LeavesAt root start (p ++ [true]) flow t) : LeavesAt root start p out t := by
  cases flow with
  | normal =>
    cases hOut
    simpa only [LeavesAt, normal_ne_halt, ↓reduceIte, destination, increment_right, atPath,
      trimPC_append_zero] using h
  | halt => cases hOut; exact h
  | repeatAt k =>
    cases k with
    | zero => simp [Flow.fromRight] at hOut
    | succ k =>
      cases hOut
      simpa only [LeavesAt, repeatAt_ne_halt, ↓reduceIte, destination, List.reverse_append,
        List.reverse_singleton, List.reverse_nil, List.nil_append, List.singleton_append, stripMany_hit] using h
  | escape k =>
    cases hOut
    simpa only [LeavesAt, escape_ne_halt, ↓reduceIte, destination, List.reverse_append,
      List.reverse_singleton, List.reverse_nil, List.nil_append, List.singleton_append, stripMany_miss (by decide : true ≠ false)]
      using h

private theorem left_normal {root : Program} {p : List Bool} {s t : Store}
    (h : LeavesAt root (atPath (p ++ [false]) s) (p ++ [false]) .normal t) :
    Positive root (atPath p s) (atPath (p ++ [true]) t) := by
  simpa only [LeavesAt, normal_ne_halt, ↓reduceIte, destination, increment_left, atPath,
    trimPC_append_zero] using h

private theorem return_to_sequence {root : Program} {p : List Bool} {s t : Store}
    (h : LeavesAt root (atPath (p ++ [true]) s) (p ++ [true]) (.repeatAt 0) t) :
    Positive root (atPath (p ++ [true]) s) (atPath p t) := by
  simpa only [LeavesAt, repeatAt_ne_halt, ↓reduceIte, destination, List.reverse_append,
    List.reverse_singleton, List.reverse_nil, List.nil_append, List.singleton_append, stripMany_hit, stripMany, stripThrough, ↓reduceIte, List.reverse_reverse] using h

/-- A structured execution is realized by the literal path operations.
Normal continuations take at least one register-program step. -/
theorem Executes.realizes {root subtree : Program} {s t : Store} {out : Flow}
    (structured : Executes subtree s out t) (p : List Bool) (located : locate root p = some subtree) :
    LeavesAt root (atPath p s) p out t := by
  induction structured generalizing p with
  | instruction op s =>
    have h := step_at_op located s
    cases effect : op.effect s with
    | mk out final =>
      rw [effect] at h
      by_cases stopped : out = .halt
      · simp only [stopped, LeavesAt, ↓reduceIte] at h ⊢
        exact .stop h
      · simp only [stopped, LeavesAt, ↓reduceIte] at h ⊢
        exact ⟨_, h, .refl⟩
  | leftExit execution previous ih =>
    have h := leave_left p previous (ih (p ++ [false]) (locate_left located))
    simpa only [atPath, trimPC_append_zero] using h
  | rightExit execLeft execRight previous ihL ihR =>
    have left := left_normal (ihL (p ++ [false]) (locate_left located))
    have right := leave_right p previous (ihR (p ++ [true]) (locate_right located))
    exact right.prepend left
  | reenter execLeft execRight execAgain ihL ihR ihRest =>
    have left := left_normal (ihL (p ++ [false]) (locate_left located))
    have right := return_to_sequence (ihR (p ++ [true]) (locate_right located))
    exact (ihRest p located).prepend (left.trans right)

end PalomarI3380.Compiler
