module
public import I3_334Support.Logic.Target
@[expose] public section

namespace PalomarI3380.Logic

theorem ArithmeticSigma1Sound.consistent (h : ArithmeticSigma1Sound) : ZFCI3Consistent := by
  intro contradiction
  let falseArithmetic : SigmaFormula := .atom .zero .zero true false
  have rep : RepresentsArithmetic falseArithmetic .bot := by
    refine ⟨trivial,fun V E _ _ s env _ => ?_⟩
    change False ↔ ∃ a b, Internal.Empty E a ∧ Internal.Empty E b ∧ a ≠ b
    constructor
    · exact False.elim
    · rintro ⟨a,b,emptyA,emptyB,different⟩
      apply different
      have model := ‹ZFCI3Model E› fixedExt (Or.inl (Or.inl (by simp [FixedAxiom]))) s
      exact model a b (fun x hx => (emptyA x hx).elim) (fun x hx => (emptyB x hx).elim)
  exact (h falseArithmetic ⟨trivial,trivial⟩ .bot rep contradiction (fun _ => 0)) rfl

end PalomarI3380.Logic
