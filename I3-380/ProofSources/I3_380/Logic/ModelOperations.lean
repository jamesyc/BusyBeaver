module
public import I3_380.Logic.NamedParameters
public import I3_380.Logic.SatisfactionSemantics
@[expose] public section

namespace PalomarI3380.Logic

variable {V : Type} {E : V → V → Prop}

def ZFCModel (E : V → V → Prop) : Prop :=
  ∀ p, Axiom p ∨ p = choiceAxiom → ∀ env, eval E p env

theorem ZFCI3Model.zfc (h : ZFCI3Model E) : ZFCModel E :=
  fun p hp env => h p (hp.elim Or.inl (fun e => Or.inr (Or.inl e))) env

theorem ZFCI3Model.has_i3 (h : ZFCI3Model E) (env : Nat → V) : Internal.HasI3 E :=
  SetFormula.holds_i3.mp (h i3Axiom (Or.inr (Or.inr rfl)) env)

theorem allPrefix_elim {p : Formula} (n : Nat) (h : ∀ env, eval E (allPrefix n p) env) :
    ∀ env, eval E p env := by
  induction n with
  | zero => exact h
  | succ n ih =>
    apply ih
    intro env
    let tail := fun i => env (i + 1)
    have same : pushValue tail (env 0) = env := by
      funext i
      cases i <;> rfl
    exact same ▸ h tail (env 0)

namespace ZFCModel

variable (h : ZFCModel E)
include h

theorem extensional (env : Nat → V) : Internal.Extensional E := by
  have ax := h fixedExt (Or.inl (Or.inl (by simp [FixedAxiom]))) env
  exact fun x y eq => ax x y (fun p => (eq p).mp) (fun p => (eq p).mpr)

theorem empty (env : Nat → V) : ∃ a, Internal.Empty E a :=
  h fixedEmpty (Or.inl (Or.inl (by simp [FixedAxiom]))) env

theorem pairing (env : Nat → V) (a b : V) : ∃ p, Internal.Pair E a b p := by
  obtain ⟨p, hp⟩ := h fixedPair (Or.inl (Or.inl (by simp [FixedAxiom]))) env a b
  exact ⟨p, fun x => ⟨(hp x).1,(hp x).2⟩⟩

theorem union (env : Nat → V) (a : V) :
    ∃ u, ∀ x, E x u ↔ ∃ y, E y a ∧ E x y := by
  obtain ⟨p, hp⟩ := h fixedUnion (Or.inl (Or.inl (by simp [FixedAxiom]))) env a
  exact ⟨p,fun x => ⟨(hp x).1,(hp x).2⟩⟩

theorem power (env : Nat → V) (a : V) :
    ∃ u, ∀ x, E x u ↔ ∀ y, E y x → E y a := by
  obtain ⟨p, hp⟩ := h fixedPower (Or.inl (Or.inl (by simp [FixedAxiom]))) env a
  exact ⟨p,fun x => ⟨(hp x).1,(hp x).2⟩⟩

theorem omega (env : Nat → V) : ∃ w, Internal.Omega E w := by
  obtain ⟨w, data⟩ := h fixedOmega (Or.inl (Or.inl (by simp [FixedAxiom]))) env
  refine ⟨w, ?_⟩
  simpa only [Internal.Omega, Internal.Inductive, Internal.Empty, Internal.Succ, iff_def, eval, pushValue] using data

theorem foundation (env : Nat → V) (a : V) (hasMember : ∃ x, E x a) :
    ∃ x, E x a ∧ ∀ y, E y x → ¬E y a :=
  h fixedFoundation (Or.inl (Or.inl (by simp [FixedAxiom]))) env a hasMember

theorem choice (env : Nat → V) (family : V) (nonempty : ∀ a, E a family → ∃ x, E x a) :
    ∃ f, Internal.FunctionOn E f family ∧
      ∀ x y, E x family → Internal.At E f x y → E y x := by
  have ax := h choiceAxiom (Or.inr rfl) env
  have own := (eval_congr_bound choiceAxiom choice_closed
    (t := SetFormula.assignment 0 env (env 0)) (fun i hi => by omega)).mp ax
  let p := SetFormula.every fun family =>
    SetFormula.implies (SetFormula.eachIn family fun x =>
      SetFormula.someIn x fun y => SetFormula.eq y y)
      (SetFormula.someSet fun f => SetFormula.both (SetFormula.functionOn f family)
        (SetFormula.eachIn family fun x => SetFormula.every fun y =>
          SetFormula.implies (SetFormula.graphValue f x y) (SetFormula.mem y x)))
  change SetFormula.holds E p 0 env (env 0) at own
  simp (disch := omega) only [p, SetFormula.holds_every, SetFormula.holds_implies, SetFormula.holds_eachIn,
    SetFormula.holds_someIn, SetFormula.holds_eq, SetFormula.holds_someSet, SetFormula.holds_both,
    SetFormula.holds_functionOn, SetFormula.holds_graphValue, SetFormula.holds_mem, SetFormula.assign_here,
    SetFormula.assign_earlier, and_true] at own
  obtain ⟨f, hf, value⟩ := own family nonempty
  exact ⟨f,hf,fun x y hx hy => value x hx y hy⟩

theorem separation_open {p : Formula} {n : Nat} (bound : Bound p (n + 1))
    (env : Nat → V) (source : V) :
    ∃ output, ∀ x, E x output ↔ E x source ∧ eval E p (pushValue env x) := by
  have ax := h (separationSchema n p) (Or.inl (Or.inr (Or.inl ⟨n,p,bound,rfl⟩)))
  exact (eval_separation p env).mp (allPrefix_elim n ax env) source

theorem replacement_open {p : Formula} {n : Nat} (bound : Bound p (n + 2))
    (env : Nat → V)
    (functional : ∀ x y z, eval E p (pushValue (pushValue env y) x) →
      eval E p (pushValue (pushValue env z) x) → y = z) (source : V) :
    ∃ output, ∀ y, E y output ↔ ∃ x, E x source ∧ eval E p (pushValue (pushValue env y) x) := by
  have ax := h (replacementSchema n p) (Or.inl (Or.inr (Or.inr ⟨n,p,bound,rfl⟩)))
  exact (eval_replacement p env).mp (allPrefix_elim n ax env) functional source

theorem separation_binary {r : V → V → Prop}
    (definition : Expanded.Binary E (fun _ _ => False) r) (source anchor : V) :
    ∃ output, ∀ x, E x output ↔ E x source ∧ r x anchor := by
  obtain ⟨n,p,parameters,scope,meaning⟩ := Expanded.lower_binary E definition source
  obtain ⟨target, contents⟩ := h.separation_open (n := n + 1) scope (pushValue parameters anchor) source
  exact ⟨target, fun x => (contents x).trans (and_congr_right fun _ => meaning x anchor)⟩

theorem replacement_binary {r : V → V → Prop}
    (definition : Expanded.Binary E (fun _ _ => False) r)
    (functional : ∀ x y z, r x y → r x z → y = z) (source : V) :
    ∃ output, ∀ y, E y output ↔ ∃ x, E x source ∧ r x y := by
  obtain ⟨n,p,parameters,scope,meaning⟩ := Expanded.lower_binary E definition source
  obtain ⟨target, contents⟩ := h.replacement_open scope parameters
    (fun x y z hy hz => functional x y z ((meaning x y).mp hy) ((meaning x z).mp hz)) source
  exact ⟨target, fun y => (contents y).trans (exists_congr fun x => and_congr_right fun _ => meaning x y)⟩

end ZFCModel
end PalomarI3380.Logic
