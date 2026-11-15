module
public import M209.Literal
@[expose] public section
namespace M209
open M6.Zip

/-- State-only renaming leaves the whole tape and its orientation unchanged. -/
def mapConf (f : Nat → Nat) (c : Conf) : Conf := ⟨f c.q, c.l, c.r⟩

/-- Generic row simulation. The inverse premise must be proved for the generated
permutation before this lemma can bind native/runtime results to literal209. -/
theorem renamed_row (inverse_law : ∀ q, forward (inverse q) = q) (q : Nat) (b : Bool) :
    (renamed q b).map (fun (w,d,t) => (w,d,forward t)) = literal (forward q) b := by
  simp only [renamed, Option.map_map]
  cases h : literal (forward q) b with
  | none => rfl
  | some row =>
    obtain ⟨w,d,t⟩ := row
    simp [inverse_law]

theorem renamed_step (inverse_law : ∀ q, forward (inverse q) = q) (c : Conf) :
    (step renamed c).map (mapConf forward) = step literal (mapConf forward c) := by
  obtain ⟨q,l,r⟩ := c
  simp only [step, renamed, mapConf]
  cases h : literal (forward q) (r.headD false) with
  | none => rfl
  | some row =>
    obtain ⟨w,d,t⟩ := row
    cases d <;> simp [Option.map, zc, zl, mapConf, inverse_law]

/-- Finite runs preserve their exact length under state conjugacy. -/
theorem renamed_run (inverse_law : ∀ q, forward (inverse q) = q) (k : Nat) (c : Conf) :
    (run renamed k c).map (mapConf forward) = run literal k (mapConf forward c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    have hs := renamed_step inverse_law c
    cases he : step renamed c with
    | none =>
      have hl : step literal (mapConf forward c) = none := by simpa [he] using hs.symm
      simp [run, he, hl]
    | some next =>
      have hl : step literal (mapConf forward c) = some (mapConf forward next) := by
        simpa [he] using hs.symm
      simp [run, he, hl, ih]

theorem renamed_reach1 (inverse_law : ∀ q, forward (inverse q) = q)
    {a b : Conf} (h : Reach1 renamed a b) :
    Reach1 literal (mapConf forward a) (mapConf forward b) := by
  obtain ⟨k,hk⟩ := h
  refine ⟨k, ?_⟩
  rw [← renamed_run inverse_law, hk]
  rfl
end M209
