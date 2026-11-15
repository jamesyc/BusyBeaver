module
public import NumericSource
@[expose] public section
namespace ZFR
open C209Soundness

/-- Numerical trace validity: the exact zero/cons recursion of
proof_sequence.mm0 traceValid, independently on all natural codes. -/
def numericTraceValid (R : Nat → Nat → Prop) (n : Nat) : Prop :=
  if h : n = 0 then True else
  let p := unpair (n-1)
  numericTraceValid R p.2 ∧ R p.1 p.2
termination_by n
decreasing_by
  have := unpair_right_le (n-1)
  omega

theorem numericTraceValid_zero (R : Nat → Nat → Prop) : numericTraceValid R 0 := by
  rw [numericTraceValid]; trivial

theorem numericTraceValid_cons (R : Nat → Nat → Prop) (r xs : Nat) :
    numericTraceValid R (cantor r xs + 1) ↔ numericTraceValid R xs ∧ R r xs := by
  rw [numericTraceValid]
  simp [sourceUnpair_pair]

attribute [local instance] Classical.propDecidable

def numericTraceDerives (R : Nat → Nat → Prop) (p r : Nat) :=
  numericTraceValid R p ∧ sourceMember r p

theorem Trace.encode_valid {R : Nat → Nat → Prop}
    (hr : ∀ r xs, Rule r xs → R (encodeRow r) (encodeTrace xs))
    {xs : List Row} (hx : Trace xs) : numericTraceValid R (encodeTrace xs) := by
  induction hx with
  | nil => exact numericTraceValid_zero R
  | @cons r xs h ht ih =>
    exact (numericTraceValid_cons R _ _).mpr ⟨ih, hr r xs h⟩

theorem ND.encode_derives {R : Nat → Nat → Prop}
    (hr : ∀ r xs, Rule r xs → R (encodeRow r) (encodeTrace xs))
    {r : Row} (h : ND r) : ∃ p, numericTraceDerives R p (encodeRow r) := by
  obtain ⟨xs, hx, hm⟩ := h.hasTrace
  exact ⟨encodeTrace xs, hx.encode_valid hr,
    (sourceMember_encode_iff encodeRow_injective r xs).mpr hm⟩

end ZFR
