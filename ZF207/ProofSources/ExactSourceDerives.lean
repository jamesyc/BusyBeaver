module
public import NumericRules
public import NumericTrace
@[expose] public section
namespace ZFR

/-- Exact union of source propositional and quantifier rule relations,
with their existential previous-row witnesses and result well-formedness.
The numeric case predicates are independent definitions on Nat. -/
def sourceFullRules (r xs : Nat) : Prop :=
  sourceBase r ∨ (∃ p, sourceMember p xs ∧ sourceUnary p r) ∨
    ∃ p q, sourceMember p xs ∧ sourceMember q xs ∧ sourceBinary p q r

def sourceFullDerives (p r : Nat) := numericTraceDerives sourceFullRules p r

theorem Rule.encode {r : Row} {xs : List Row} (hr : Rule r xs) :
    sourceFullRules (encodeRow r) (encodeTrace xs) := by
  rcases hr with hb | ⟨p,hp,hu⟩ | ⟨p,q,hp,hq,hb⟩
  · exact Or.inl hb.encode
  · exact Or.inr (Or.inl ⟨encodeRow p,
      (sourceMember_encode_iff encodeRow_injective p xs).mpr hp, hu.encode⟩)
  · exact Or.inr (Or.inr ⟨encodeRow p,encodeRow q,
      (sourceMember_encode_iff encodeRow_injective p xs).mpr hp,
      (sourceMember_encode_iff encodeRow_injective q xs).mpr hq,hb.encode⟩)

/-- Typed derivations compile to independently checked exact numeric source
traces. This does not supply missing ZFR axiom derivations. -/
theorem ND.exact_numeric_derives {r : Row} (h : ND r) :
    ∃ p, sourceFullDerives p (encodeRow r) :=
  h.encode_derives (fun _ _ h => h.encode)

end ZFR
