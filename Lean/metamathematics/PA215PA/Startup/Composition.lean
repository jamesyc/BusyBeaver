import PA215PA.NatTape

namespace PA215.PA.NatTape

theorem run_add (m n : Nat) (s : Configuration) :
    run (m+n) s = (run m s).bind (run n) := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih =>
    cases h : step s <;> simp [Nat.succ_add,run,h,ih]

theorem run_trans {m n : Nat} {a b c : Configuration}
    (h₁ : run m a = some b) (h₂ : run n b = some c) :
    run (m+n) a = some c := by
  rw [run_add,h₁]
  exact h₂

end PA215.PA.NatTape
