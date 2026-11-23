module
public import I3_334Support.Arithmetic.InternalConfiguration
public import I3_334Support.Logic.TapeFormulas
@[expose] public section

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SquareRepresentation ArithmeticMachine

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "K" => (L.context inhabited)
local notation "W" => D.Points
local instance : (W)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano

def configurationArguments (q l r z : Argument V) : Nat → Argument V
  | 0 => q
  | 1 => l
  | 2 => r
  | _ => z

def configurationAt (q l r z : Argument V) : Formula V :=
  applyTemplate (SetFormula.configCode ⟨0,1,2⟩ 3) 4 (configurationArguments q l r z)

theorem configurationAt_scope {n : Nat} {q l r z : Argument V}
    (hq : q.bound n) (hl : l.bound n) (hr : r.bound n) (hz : z.bound n) :
    Bound (configurationAt q l r z) n := by
  apply applyTemplate_scope _ (SetFormula.scope_configCode (d := 4) (c := ⟨0,1,2⟩) (code := 3) (by simp [SetFormula.inScope]) (by decide))
  intro i _
  cases i with
  | zero => exact hq
  | succ i =>
    cases i with
    | zero => exact hl
    | succ i =>
      cases i with
      | zero => exact hr
      | succ i => exact hz

theorem configurationAt_eval (q l r z : Argument V) (env : Nat → V) :
    eval E G (configurationAt q l r z) env ↔
      Internal.ConfigurationCode E ⟨q.value env,l.value env,r.value env⟩ (z.value env) := by
  exact (applyTemplate_eval _ (SetFormula.scope_configCode (d := 4) (c := ⟨0,1,2⟩) (code := 3) (by simp [SetFormula.inScope]) (by decide)) _ env).trans
    (SetFormula.holds_configCode (d := 4) (c := ⟨0,1,2⟩) (code := 3) (by simp [SetFormula.inScope]) (by decide))

end PalomarI3380.Logic.Expanded.OmegaDomain
