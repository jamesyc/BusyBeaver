module
public import I3_380.Arithmetic.TranslateFormula
@[expose] public section

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open SquareRepresentation

variable {V ξ : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "K" => (L.context inhabited)

/-- Every arithmetic formula, with parameters interpreted in the actual
omega of the set model, supports induction by Separation. -/
theorem induction (p : FFL.FirstOrder.Semiformula ℒₒᵣ ξ 1) (params : ξ → D.Points)
    (zero : p.Eval (fun _ => 0) params)
    (next : ∀ n : D.Points, p.Eval (fun _ => n) params → p.Eval (fun _ => D.successor n) params) :
    ∀ n : D.Points, p.Eval (fun _ => n) params := by
  let form := translateFormula p (.named D.omega) (fun _ => .variable 0)
    (fun i => .named (params i).val)
  let P := fun x => eval E G form (fun _ => x)
  let R := fun x (_ : V) => P x
  have scope : Bound form 1 :=
    translateFormula_scope p trivial (fun _ => Nat.zero_lt_succ _) (fun _ => trivial)
  have describes : Binary E G R :=
    ⟨form,bound_extension scope (by decide),fun env =>
      eval_congr E G form scope (fun i hi => by
        have eq : i = 0 := by omega
        subst i
        rfl)⟩
  have meaning (x : D.Points) :
      P x.val ↔ p.Eval (fun _ => x) params :=
    translateFormula_eval D p (.named D.omega) _ _ _ _ params rfl (fun _ => rfl) (fun _ => rfl)
  obtain ⟨cut,spec⟩ := L.separation R describes D.omega (K).empty
  have inductiveCut : Internal.Inductive E cut := by
    have zeroIn : E (0 : D.Points).val cut := (spec _).mpr
      ⟨(0 : D.Points).property,(meaning 0).mpr zero⟩
    refine ⟨⟨(K).empty,(K).empty_mem,zeroIn⟩,fun x hx => ?_⟩
    obtain ⟨inOmega,valid⟩ := (spec x).mp hx
    let n : D.Points := ⟨x,inOmega⟩
    exact ⟨(D.successor n).val,(K).mem_succ x,
      (spec _).mpr ⟨(D.successor n).property,(meaning (D.successor n)).mpr (next n ((meaning n).mp valid))⟩⟩
  intro n
  exact (meaning n).mp ((spec _).mp (D.specification.2 cut inductiveCut _ n.property)).2

theorem induction_via (p : FFL.FirstOrder.Semiformula ℒₒᵣ ξ 1) (params : ξ → D.Points)
    {P : D.Points → Prop} (meaning : ∀ x, p.Eval (fun _ => x) params ↔ P x)
    (zero : P 0) (step : ∀ x, P x → P (D.successor x)) (x : D.Points) : P x :=
  (meaning x).mp (D.induction p params ((meaning 0).mpr zero)
    (fun x h => (meaning _).mpr (step x ((meaning _).mp h))) x)

end PalomarI3380.Logic.Expanded.OmegaDomain
