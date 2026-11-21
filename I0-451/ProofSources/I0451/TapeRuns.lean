module
public import I0451.Window

/-! Reusable one-cell moves and repeated scans on the packed tape. -/

@[expose] public section
namespace I0451

/-- Add known cells in head-first order to a side of the packed tape. -/
def pack (cells : List Bool) (tail : Nat) : Nat := cells.foldr push tail

@[simp] theorem pack_nil (tail : Nat) : pack [] tail = tail := rfl
@[simp] theorem pack_cons (b : Bool) (cells : List Bool) (tail : Nat) :
    pack (b :: cells) tail = push b (pack cells tail) := rfl

theorem pack_append (xs ys : List Bool) (tail : Nat) :
    pack (xs ++ ys) tail = pack xs (pack ys tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem pack_repeat_last (b : Bool) (n tail : Nat) :
    pack (List.replicate (n + 1) b) tail = pack (List.replicate n b) (push b tail) := by
  rw [List.replicate_succ', pack_append]
  rfl

theorem pack_repeats (b : Bool) (m n tail : Nat) :
    pack (List.replicate m b) (pack (List.replicate n b) tail) =
      pack (List.replicate (m + n) b) tail := by
  rw [← pack_append, List.replicate_append_replicate]

/-- Encoding of a nonterminal row in the literal table. -/
def transition (write right : Bool) (next : Nat) : Nat :=
  4 * next + 2 * right.toNat + write.toNat + 1

theorem step_right {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write true t) (l r : Nat) :
    step table ⟨q, l, push read r⟩ = some ⟨t, push write l, r⟩ := by
  simp only [step, bit_push, edge, transition]
  have state : (4 * t + 2 * true.toNat + write.toNat) / 4 = t := by
    cases write <;> simp <;> omega
  have direction : bit ((4 * t + 2 * true.toNat + write.toNat) / 2) = true := by
    cases write <;> simp [bit] <;> omega
  have cell : bit (4 * t + 2 * true.toNat + write.toNat) = write := by
    cases write <;> simp [bit] <;> omega
  simp only [move, direction, ite_true, cell, state, pop_push]

theorem step_left {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write false t) (a : Bool) (l r : Nat) :
    step table ⟨q, push a l, push read r⟩ = some ⟨t, l, push a (push write r)⟩ := by
  simp only [step, bit_push, edge, transition]
  have state : (4 * t + 2 * false.toNat + write.toNat) / 4 = t := by
    cases write <;> simp <;> omega
  have direction : bit ((4 * t + 2 * false.toNat + write.toNat) / 2) = false := by
    cases write <;> simp [bit] <;> omega
  have cell : bit (4 * t + 2 * false.toNat + write.toNat) = write := by
    cases write <;> simp [bit] <;> omega
  simp only [move, direction, Bool.false_eq_true, ite_false, cell, state, bit_push, pop_push]

def Reaches (table : Table) (first last : Config) : Prop :=
  ∃ n, run table n first = some last

namespace Reaches

theorem step {table : Table} {first last : Config} (h : I0451.step table first = some last) :
    Reaches table first last :=
  ⟨1, by simp only [run, h, Option.bind]⟩

theorem trans {table : Table} {first middle last : Config}
    (a : Reaches table first middle) (b : Reaches table middle last) :
    Reaches table first last := by
  obtain ⟨m, a⟩ := a
  obtain ⟨n, b⟩ := b
  exact ⟨m + n, run_join a b rfl⟩

theorem right {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write true t) (l r : Nat) :
    Reaches table ⟨q, l, push read r⟩ ⟨t, push write l, r⟩ :=
  .step (step_right edge l r)

theorem left {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write false t) (a : Bool) (l r : Nat) :
    Reaches table ⟨q, push a l, push read r⟩ ⟨t, l, push a (push write r)⟩ :=
  .step (step_left edge a l r)

end Reaches

theorem scan_right {table : Table} {q : Nat} {read write : Bool}
    (edge : row table q read = transition write true q) (n l r : Nat) :
    run table n ⟨q, l, pack (List.replicate n read) r⟩ =
      some ⟨q, pack (List.replicate n write) l, r⟩ := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, pack_cons, run, step_right edge]
    have endTape : pack (List.replicate (n + 1) write) l =
        pack (List.replicate n write) (push write l) := by
      rw [List.replicate_succ', pack_append]
      rfl
    rw [endTape]
    exact ih (push write l)

/-- Scan left over the current cell and the next `n - 1` known cells,
leaving the head on an untouched sentinel. -/
theorem scan_left {table : Table} {q : Nat} {read write : Bool}
    (edge : row table q read = transition write false q) (n : Nat) (sentinel : Bool)
    (l r : Nat) :
    run table n ⟨q, pack (List.replicate n read) (push sentinel l) / 2,
      push (bit (pack (List.replicate n read) (push sentinel l))) r⟩ =
      some ⟨q, l, push sentinel (pack (List.replicate n write) r)⟩ := by
  induction n generalizing r with
  | zero => simp [run]
  | succ n ih =>
    rw [List.replicate_succ, pack_cons, bit_push, pop_push]
    generalize h : pack (List.replicate n read) (push sentinel l) = left
    have decompose := push_bit_pop left
    rw [← decompose, run, step_left edge]
    rw [← h]
    have endTape : pack (List.replicate (n + 1) write) r =
        pack (List.replicate n write) (push write r) := by
      rw [List.replicate_succ', pack_append]
      rfl
    rw [endTape]
    exact ih (push write r)

/-- Positive-length reachability, used to rule out stuttering in an
unbounded simulation. -/
def Advances (table : Table) (first last : Config) : Prop :=
  ∃ n, 0 < n ∧ run table n first = some last

theorem Reaches.positive_of_state_ne {table : Table} {first last : Config}
    (reach : Reaches table first last) (different : first.state ≠ last.state) :
    Advances table first last := by
  obtain ⟨n, trace⟩ := reach
  cases n with
  | zero =>
    simp only [run, Option.some.injEq] at trace
    exact (different (congrArg Config.state trace)).elim
  | succ n => exact ⟨n + 1, Nat.zero_lt_succ _, trace⟩

theorem Advances.trans {table : Table} {first middle last : Config}
    (a : Advances table first middle) (b : Reaches table middle last) :
    Advances table first last := by
  obtain ⟨m, pos, a⟩ := a
  obtain ⟨n, b⟩ := b
  exact ⟨m + n, by omega, run_join a b rfl⟩

theorem Advances.halts {table : Table} {first last : Config}
    (progress : Advances table first last) (halt : step table last = none) : Halts table first := by
  obtain ⟨n, _, reach⟩ := progress
  exact ⟨n, last, reach, halt⟩

/-- A zipper whose head is on the first cell of its left argument. -/
def fromLeft (q l r : Nat) : Config := ⟨q, l / 2, push (bit l) r⟩

@[simp] theorem fromLeft_push (q l r : Nat) (b : Bool) :
    fromLeft q (push b l) r = ⟨q, l, push b r⟩ := by
  simp [fromLeft]

theorem Reaches.left' {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write false t) (l r : Nat) :
    Reaches table (fromLeft q (push read l) r) (fromLeft t l (push write r)) := by
  rw [fromLeft_push, ← push_bit_pop l, fromLeft_push]
  exact Reaches.left edge _ _ _

theorem Reaches.enterLeft {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write false t) (l r : Nat) :
    Reaches table ⟨q, l, push read r⟩ (fromLeft t l (push write r)) := by
  rw [← push_bit_pop l, fromLeft_push]
  exact Reaches.left edge _ _ _

theorem Reaches.leaveLeft {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write true t) (l r : Nat) :
    Reaches table (fromLeft q (push read l) r) ⟨t, push write l, r⟩ := by
  rw [fromLeft_push]
  exact Reaches.right edge l r

theorem Reaches.scanLeft {table : Table} {q : Nat} {read write : Bool}
    (edge : row table q read = transition write false q) (n l r : Nat) :
    Reaches table (fromLeft q (pack (List.replicate n read) l) r)
      (fromLeft q l (pack (List.replicate n write) r)) := by
  refine ⟨n, ?_⟩
  simpa only [fromLeft, push_bit_pop] using scan_left edge n (bit l) (l / 2) r

end I0451
