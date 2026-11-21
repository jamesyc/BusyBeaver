module
public import I3_380.Arithmetic.InternalConfiguration
public import I3_380.Logic.Halting
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- Decode the clock result at one internal arithmetic index. -/
def clockCoordinates : ArithmeticSemisentence 4 :=
  “i q l r. ∃ code, !((clockBlueprint 380 packedLiteral).resultDef) code i 0 ∧ !pair₃Def code q l r”

theorem clockCoordinates_eval {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (i q l r : M) :
    clockCoordinates.Evalb ![i,q,l,r] ↔ clock 380 packedLiteral i (0 : M) = encode q l r := by
  simp [clockCoordinates,clock_eval,pair₃_defined.iff,encode,Semiformula.eval_rew,Function.comp_def,
    Matrix.comp_vecCons',Empty.eq_elim,Matrix.empty_eq,Matrix.constant_eq_singleton]

end PalomarI3380.ArithmeticMachine

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SquareRepresentation ArithmeticMachine

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "K" => (L.context inhabited)
local notation "W" => D.Points
local instance : (W)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano

noncomputable def clockAt (i : W) : Configuration D :=
  Configuration.decode (clock 380 packedLiteral i 0)

theorem clockAt_zero : D.clockAt 0 = ⟨0,0,0⟩ := by
  have code : (⟨0,0,0⟩ : Configuration D).code = 0 := by
    simp [Configuration.code,ArithmeticMachine.encode,Arithmetic.pair]
  rw [clockAt,clock_zero]
  exact (congrArg (Configuration.decode (D := D)) code.symm).trans (Configuration.decode_encode _)

theorem clockAt_succ (i : W) :
    D.clockAt (D.successor i) = Configuration.decode (tick 380 packedLiteral (D.clockAt i).code) := by
  rw [← D.plus_one,clockAt,clock_succ]
  rw [clockAt,Configuration.encode_decode]

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

/-- A graph of literal configurations in the membership language. The
coordinates are read from the arithmetic clock and packed as actual set pairs. -/
def clockGraphFormula (omega : V) : Formula V :=
  .and (.mem (.variable 0) (.named omega))
    (.ex (.ex (.ex
      (.and (.mem (.variable 2) (.named omega))
        (.and (.mem (.variable 1) (.named omega))
          (.and (.mem (.variable 0) (.named omega))
            (.and (configurationAt (.variable 2) (.variable 1) (.variable 0) (.variable 4))
              (translateFormula clockCoordinates (.named omega)
                ![.variable 3,.variable 2,.variable 1,.variable 0] Empty.elim))))))))

theorem clockGraphFormula_scope (omega : V) : Bound (clockGraphFormula omega) 2 := by
  have q : (Argument.variable (V := V) 2).bound 5 := by change 2 < 5; decide
  have l : (Argument.variable (V := V) 1).bound 5 := by change 1 < 5; decide
  have r : (Argument.variable (V := V) 0).bound 5 := by change 0 < 5; decide
  have z : (Argument.variable (V := V) 4).bound 5 := by change 4 < 5; decide
  refine ⟨⟨Nat.zero_lt_succ _,trivial⟩,⟨⟨q,trivial⟩,⟨⟨l,trivial⟩,⟨⟨r,trivial⟩,
    configurationAt_scope q l r z,?_⟩⟩⟩⟩
  apply translateFormula_scope (region := .named omega) _ trivial _ (fun x => x.elim)
  intro j
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> simp [Argument.bound]

theorem clockGraphFormula_eval (env : Nat → V) :
    eval E G (clockGraphFormula D.omega) env ↔
      ∃ h : E (env 0) D.omega, (D.clockAt ⟨env 0,h⟩).setCode = env 1 := by
  have arithmetic (q l r : V) (hq : E q D.omega) (hl : E l D.omega) (hr : E r D.omega)
      (hi : E (env 0) D.omega) :
      let values : Fin 4 → W := ![⟨env 0,hi⟩,⟨q,hq⟩,⟨l,hl⟩,⟨r,hr⟩]
      eval E G (translateFormula clockCoordinates (.named D.omega)
        ![.variable 3,.variable 2,.variable 1,.variable 0] Empty.elim)
        (pushValue (pushValue (pushValue env q) l) r) ↔
        clock (M := W) 380 packedLiteral ⟨env 0,hi⟩ 0 = ArithmeticMachine.encode (M := W)
          (⟨q,hq⟩ : W) (⟨l,hl⟩ : W) (⟨r,hr⟩ : W) := by
    intro values
    have correct (i : Fin 4) :
        (![(Argument.variable 3 : Argument V),.variable 2,.variable 1,.variable 0] i).value
          (pushValue (pushValue (pushValue env q) l) r) = (values i).val := by
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> rfl
    exact (translateFormula_eval D _ _ _ _ _ values Empty.elim rfl correct (fun x => x.elim)).trans
      (clockCoordinates_eval ..)
  constructor
  · rintro ⟨hi,q,l,r,hq,hl,hr,ordered,computation⟩
    have coded := (configurationAt_eval _ _ _ _ _).mp ordered
    let c : Configuration D := ⟨⟨q,hq⟩,⟨l,hl⟩,⟨r,hr⟩⟩
    have exactCode : (D.clockAt ⟨env 0,hi⟩) = c := by
      simp only [clockAt]
      rw [(arithmetic q l r hq hl hr hi).mp computation]
      exact Configuration.decode_encode c
    exact ⟨hi,exactCode.symm ▸ ((c.encodes_set _).mp coded).symm⟩
  · rintro ⟨hi,eq⟩
    let c := D.clockAt ⟨env 0,hi⟩
    refine ⟨hi,c.state.val,c.left.val,c.right.val,c.state.property,c.left.property,c.right.property,
      (configurationAt_eval _ _ _ _ _).mpr ((c.encodes_set _).mpr eq.symm),?_⟩
    exact (arithmetic _ _ _ c.state.property c.left.property c.right.property hi).mpr
      ((Configuration.encode_decode (clock (M := W) 380 packedLiteral ⟨env 0,hi⟩ 0)).symm)

end PalomarI3380.Logic.Expanded.OmegaDomain
