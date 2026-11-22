module
public import ZF192Support.Logic.Source.Axioms
@[expose] public section
namespace ZFR

/-- Source proof with an explicit finite context of actual ZFR axioms. -/
def SourceTheorem (p : Formula) : Prop :=
 ∃ Γ : Context, (∀ a, a ∈ Γ → SourceAxiom a) ∧ ND (.seq Γ p)

theorem SourceTheorem.mp {p q : Formula} (hp : SourceTheorem p) (hi : SourceTheorem (.imp p q)) :
 SourceTheorem q := by
 obtain ⟨Γ,hΓ,hp⟩ := hp
 obtain ⟨Δ,hΔ,hi⟩ := hi
 refine ⟨Γ++Δ,?_,ND.ie (ND.wk (fun a ha => List.mem_append_right Γ ha) hi)
   (ND.wk (fun a ha => List.mem_append_left Δ ha) hp)⟩
 intro a ha
 rcases List.mem_append.mp ha with h | h
 · exact hΓ a h
 · exact hΔ a h

end ZFR
