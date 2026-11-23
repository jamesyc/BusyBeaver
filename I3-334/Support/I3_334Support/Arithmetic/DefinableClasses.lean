module
public import I3_334Support.Arithmetic.HistoryDomain
@[expose] public section

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open SquareRepresentation ArithmeticMachine
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "K" => (L.context inhabited)
local notation "W" => D.Points
local instance : (W)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano

theorem unary_arithmetic_class (p : ArithmeticSemisentence 1) (holds : W → Prop)
    (interpret : ∀ i : W, p.Evalb ![i] ↔ holds i) :
    Binary E G (fun x (_ : V) => ∃ h : E x D.omega, holds ⟨x,h⟩) := by
  let form : Formula V := .and (.mem (.variable 0) (.named D.omega))
    (translateFormula p (.named D.omega) (fun _ => .variable 0) Empty.elim)
  have scope : Bound form 2 :=
    ⟨⟨Nat.zero_lt_succ _,trivial⟩,translateFormula_scope _ trivial
      (fun _ => Nat.zero_lt_succ _) (fun x => x.elim)⟩
  refine ⟨form,scope,fun env => ?_⟩
  have interpretation (hi : E (env 0) D.omega) :
      eval E G (translateFormula p (.named D.omega) (fun _ => .variable 0) Empty.elim) env ↔
        holds ⟨env 0,hi⟩ :=
    (translateFormula_eval D _ _ _ _ _ (![(⟨env 0,hi⟩ : W)]) Empty.elim rfl
      (fun i => by have eq : i = 0 := Subsingleton.elim _ _; subst i; rfl) (fun x => x.elim)).trans
        (interpret _)
  exact ⟨fun ⟨hi,h⟩ => ⟨hi,(interpretation hi).mp h⟩,fun ⟨hi,h⟩ => ⟨hi,(interpretation hi).mpr h⟩⟩

end PalomarI3380.Logic.Expanded.OmegaDomain
