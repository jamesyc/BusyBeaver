module
public import I0451.Machine

public section
namespace I0451

@[simp] theorem bit_push (b : Bool) (tail : Nat) : bit (push b tail) = b := by
  cases b <;> unfold bit push <;> simp <;> omega

@[simp] theorem pop_push (b : Bool) (tail : Nat) : push b tail / 2 = tail := by
  cases b <;> unfold push <;> simp <;> omega

theorem run_add (table : Table) (m n : Nat) (c : Config) :
    run table (m + n) c = (run table m c).bind (run table n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add, run, run]
    cases h : step table c with
    | none => rfl
    | some d => exact ih d

theorem run_join {table : Table} {m n total : Nat} {a b c : Config}
    (first : run table m a = some b) (second : run table n b = some c)
    (length : m + n = total) : run table total a = some c := by
  subst total
  rw [run_add, first]
  exact second

/-- Removing rows cannot add runs. Every successful run of the smaller
table is reproduced by any extension of its rows. -/
theorem run_of_agreeing_rows {small full : Table}
    (agree : ∀ q b, row small q b ≠ 0 → row full q b = row small q b)
    {n : Nat} {a b : Config} (reach : run small n a = some b) :
    run full n a = some b := by
  induction n generalizing a with
  | zero => exact reach
  | succ n ih =>
    have next : step small a = step full a ∨ step small a = none := by
      cases h : row small a.state (bit a.right) with
      | zero => exact Or.inr (by simp only [step, h])
      | succ code =>
        have fullRow := agree a.state (bit a.right) (h ▸ Nat.succ_ne_zero code)
        exact Or.inl (by simp only [step, fullRow, h])
    rcases next with same | missing
    · cases h : step small a with
      | none => simp [run, h] at reach
      | some c =>
        simp only [run, ← same, h, Option.bind] at reach ⊢
        exact ih reach
    · simp [run, missing] at reach

theorem run_len_le_terminal {table : Table} {m n : Nat} {initial c d : Config}
    (front : run table m initial = some c) (finish : run table n initial = some d)
    (stop : step table d = none) : m ≤ n := by
  by_cases le : m ≤ n
  · exact le
  · obtain ⟨k, equation⟩ := Nat.exists_eq_add_of_le (show n + 1 ≤ m by omega)
    rw [equation, Nat.add_assoc, run_add, finish] at front
    simp [Nat.one_add, run, stop] at front

theorem halts_iff_of_run {table : Table} {m : Nat} {c d : Config}
    (prefixRun : run table m c = some d) : Halts table c ↔ Halts table d := by
  constructor
  · rintro ⟨n, e, visit, stop⟩
    have le := run_len_le_terminal prefixRun visit stop
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le le
    rw [run_add, prefixRun] at visit
    exact ⟨k, e, visit, stop⟩
  · rintro ⟨k, e, visit, stop⟩
    exact ⟨m + k, e, by rw [run_add, prefixRun]; exact visit, stop⟩

/-- Any local simulation by positive-length segments preserves halting, provided
the simulated endpoints are again related and terminal configurations agree. -/
theorem halts_of_simulation {source target : Table} {R : Config → Config → Prop}
    (simulate : ∀ {c d}, R c d →
      (step source c = none ∧ Halts target d) ∨
      ∃ (m n : Nat) (c' d' : Config),
        run source (m + 1) c = some c' ∧ run target n d = some d' ∧ R c' d') :
    ∀ {c d}, R c d → Halts source c → Halts target d := by
  rintro c d related ⟨fuel, last, reached, stopped⟩
  induction fuel using Nat.strongRecOn generalizing c d with
  | ind fuel ih =>
    rcases simulate related with ⟨_, halts⟩ | ⟨m, n, c', d', fromSource, fromTarget, next⟩
    · exact halts
    · have le := run_len_le_terminal fromSource reached stopped
      obtain ⟨k, equation⟩ := Nat.exists_eq_add_of_le le
      rw [equation, run_add, fromSource] at reached
      exact (halts_iff_of_run fromTarget).2 (ih k (by omega) next reached)

end I0451
