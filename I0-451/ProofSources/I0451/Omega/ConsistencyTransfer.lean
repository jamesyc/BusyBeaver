module
public import I0451.Omega.ArithmeticConsequences

/-! An arithmetic consistency-transfer rule. A proof of Con(T) in B
turns any coded refutation of T into a coded refutation of B. -/
@[expose] public section
namespace I0451.Omega

open FFL FFL.Entailment FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

private theorem implication_of_known (B : ArithmeticTheory) (φ : ArithmeticSentence)
    (h : B ⊢ φ) : B ⊢ (∼φ) 🡒 ⊥ := by
  cl_prover [h]

private theorem transfer_propositional (T : ArithmeticTheory) (a b c : ArithmeticSentence)
    (verification : T ⊢ (∼a) 🡒 b) (combination : T ⊢ b 🡒 c) :
    T ⊢ (∼c) 🡒 a := by
  cl_prover [verification, combination]

theorem arithmetical_consistency_transfer (B T : ArithmeticTheory)
    [B.Δ₁] [T.Δ₁] [𝗣𝗔⁻ ⪯ B] (given : B ⊢ T.standardProvability.con) :
    𝗜𝚺₁ ⊢ B.consistent.val 🡒 T.standardProvability.con := by
  let conT : ArithmeticSentence := T.standardProvability.con
  have refutationIsSigmaOne : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (∼conT) := by
    simp [conT, ProvabilityAbstraction.Provability.con, standardProvability_def]
  have verify : 𝗜𝚺₁ ⊢ (∼conT) 🡒 B.standardProvability (∼conT) :=
    provable_sigma_one_complete (T := B) refutationIsSigmaOne
  have conflict := implication_of_known B conT given
  have combine : 𝗜𝚺₁ ⊢ B.standardProvability (∼conT) 🡒 B.standardProvability ⊥ :=
    ProvabilityAbstraction.Provability.mono (𝔅 := B.standardProvability) conflict
  exact transfer_propositional _ conT _ _ verify combine

end I0451.Omega
