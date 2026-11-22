module
public import ZF192Support.Logic.Source.Schemas.Definitions
@[expose] public section
namespace ZFR

export PalomarZF192Theory (fixedRefl fixedSym fixedTrans fixedEqElem fixedExt fixedEmpty
  fixedPair fixedUnion fixedPower fixedOmega fixedFoundation)

abbrev SourceFixedAxiom := PalomarZF192Theory.FixedAxiom
abbrev SourceAxiom := PalomarZF192Theory.Axiom

theorem _root_.PalomarZF192Theory.Axiom.closed {p : Formula} (h : SourceAxiom p) : Bound p 0 := by
  rcases h with h | ⟨n, body, hb, rfl⟩ | ⟨n, body, hb, rfl⟩
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [fixedRefl, fixedSym, fixedTrans, fixedEqElem, fixedExt, fixedEmpty,
        fixedPair, fixedUnion, fixedPower, fixedOmega, fixedFoundation, Bound]
  · exact separationSchema_closed n body hb
  · exact replacementSchema_closed n body hb

theorem separationSchema_in_zfr (n : Nat) (p : Formula) (hp : Bound p (n + 1)) :
    SourceAxiom (separationSchema n p) :=
  Or.inr (Or.inl ⟨n, p, hp, rfl⟩)

theorem replacementSchema_in_zfr (n : Nat) (p : Formula) (hp : Bound p (n + 2)) :
    SourceAxiom (replacementSchema n p) :=
  Or.inr (Or.inr ⟨n, p, hp, rfl⟩)

end ZFR
