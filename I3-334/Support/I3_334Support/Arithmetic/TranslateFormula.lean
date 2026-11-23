module
public import I3_334Support.Arithmetic.TranslateTerm
@[expose] public section

namespace PalomarI3380.Logic.Expanded

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open SquareRepresentation

variable {V : Type} {ξ : Type} {E G : V → V → Prop} {n : Nat}

def arithmeticAtom (less : Bool) (terms : Fin 2 → FFL.FirstOrder.Semiterm ℒₒᵣ ξ n)
    (bound : Fin n → Argument V) (free : ξ → Argument V) : Formula V :=
  let left := translateTerm (terms 0) (Argument.up ∘ bound) (Argument.up ∘ free) (.variable 0)
  let right := translateTerm (terms 1) (Argument.up ∘ Argument.up ∘ bound)
    (Argument.up ∘ Argument.up ∘ free) (.variable 0)
  let compare := if less then Formula.mem (.variable 1) (.variable 0)
    else Formula.eq (.variable 1) (.variable 0)
  .ex (.and left (.ex (.and right compare)))

def boundUnderBinder (b : Fin n → Argument V) : Fin (n+1) → Argument V :=
  Fin.cons (.variable 0) (Argument.up ∘ b)

def translateFormula : {n : Nat} → FFL.FirstOrder.Semiformula ℒₒᵣ ξ n → Argument V →
    (Fin n → Argument V) → (ξ → Argument V) → Formula V
  | _, .verum, _, _, _ => .imp .bot .bot
  | _, .falsum, _, _, _ => .bot
  | _, .rel .eq terms, _, b, f => arithmeticAtom false terms b f
  | _, .rel .lt terms, _, b, f => arithmeticAtom true terms b f
  | _, .nrel .eq terms, _, b, f => neg (arithmeticAtom false terms b f)
  | _, .nrel .lt terms, _, b, f => neg (arithmeticAtom true terms b f)
  | _, .and p q, ω, b, f => .and (translateFormula p ω b f) (translateFormula q ω b f)
  | _, .or p q, ω, b, f => .or (translateFormula p ω b f) (translateFormula q ω b f)
  | _, .all p, ω, b, f =>
    .all (.imp (.mem (.variable 0) ω.up)
      (translateFormula p ω.up (boundUnderBinder b) (Argument.up ∘ f)))
  | _, .exs p, ω, b, f =>
    .ex (.and (.mem (.variable 0) ω.up)
      (translateFormula p ω.up (boundUnderBinder b) (Argument.up ∘ f)))

theorem arithmeticAtom_scope (less : Bool) (terms : Fin 2 → FFL.FirstOrder.Semiterm ℒₒᵣ ξ n)
    {d : Nat} {b : Fin n → Argument V} {f : ξ → Argument V}
    (hb : ∀ i, (b i).bound d) (hf : ∀ i, (f i).bound d) : Bound (arithmeticAtom less terms b f) d := by
  refine ⟨translateTerm_scope _ (fun i => Argument.bound_shift (hb i))
    (fun i => Argument.bound_shift (hf i)) (Nat.zero_lt_succ _),
    translateTerm_scope _ (fun i => Argument.bound_shift (Argument.bound_shift (hb i)))
      (fun i => Argument.bound_shift (Argument.bound_shift (hf i))) (Nat.zero_lt_succ _),?_⟩
  cases less <;> exact ⟨Nat.succ_lt_succ (Nat.zero_lt_succ _),Nat.zero_lt_succ _⟩

theorem translateFormula_scope (p : FFL.FirstOrder.Semiformula ℒₒᵣ ξ n)
    {d : Nat} {region : Argument V} {b : Fin n → Argument V} {f : ξ → Argument V}
    (hw : region.bound d) (hb : ∀ i, (b i).bound d) (hf : ∀ i, (f i).bound d) :
    Bound (translateFormula p region b f) d := by
  induction p generalizing d region f with
  | verum => exact ⟨trivial,trivial⟩
  | falsum => trivial
  | rel r terms =>
    cases r with
    | eq => exact arithmeticAtom_scope false terms hb hf
    | lt => exact arithmeticAtom_scope true terms hb hf
  | nrel r terms =>
    cases r with
    | eq => exact ⟨arithmeticAtom_scope false terms hb hf,trivial⟩
    | lt => exact ⟨arithmeticAtom_scope true terms hb hf,trivial⟩
  | and p q ip iq | or p q ip iq => exact ⟨ip hw hb hf,iq hw hb hf⟩
  | all p ih | exs p ih =>
    have atZero : (Argument.variable (V := V) 0).bound (d+1) := Nat.zero_lt_succ _
    have inside := Argument.bound_shift hw
    refine ⟨⟨atZero,inside⟩,ih inside (fun i => ?_) (fun j => Argument.bound_shift (hf j))⟩
    exact Fin.cases atZero (fun j => Argument.bound_shift (hb j)) i

variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

theorem arithmeticAtom_eval (less : Bool) (terms : Fin 2 → FFL.FirstOrder.Semiterm ℒₒᵣ ξ n)
    (bound : Fin n → Argument V) (free : ξ → Argument V) (env : Nat → V)
    (values : Fin n → D.Points) (params : ξ → D.Points)
    (bv : ∀ i, (bound i).value env = (values i).val)
    (fv : ∀ i, (free i).value env = (params i).val) :
    eval E G (arithmeticAtom less terms bound free) env ↔
    if less then (terms 0).val values params < (terms 1).val values params
    else (terms 0).val values params = (terms 1).val values params := by
  have hleft (x : V) := translateTerm_eval D (terms 0) (Argument.up ∘ bound) (Argument.up ∘ free)
    (.variable 0) (pushValue env x) values params
    (fun i => (Argument.value_shift _ _ _).trans (bv i)) (fun i => (Argument.value_shift _ _ _).trans (fv i))
  have hright (x y : V) := translateTerm_eval D (terms 1) (Argument.up ∘ Argument.up ∘ bound)
    (Argument.up ∘ Argument.up ∘ free) (.variable 0) (pushValue (pushValue env x) y) values params
    (fun i => (Argument.value_shift _ _ _).trans ((Argument.value_shift _ _ _).trans (bv i)))
    (fun i => (Argument.value_shift _ _ _).trans ((Argument.value_shift _ _ _).trans (fv i)))
  cases less
  · simp only [arithmeticAtom,Bool.false_eq_true,eval,hleft,hright,Argument.value,pushValue,
      exists_eq_left]
    exact Subtype.ext_iff.symm
  · simp only [arithmeticAtom,ite_eq_left,eval,hleft,hright,Argument.value,pushValue,
      exists_eq_left]
    exact Iff.rfl

theorem translateFormula_eval (p : FFL.FirstOrder.Semiformula ℒₒᵣ ξ n) (region : Argument V)
    (bound : Fin n → Argument V) (free : ξ → Argument V) (env : Nat → V)
    (values : Fin n → D.Points) (params : ξ → D.Points) (hw : region.value env = D.omega)
    (bv : ∀ i, (bound i).value env = (values i).val) (fv : ∀ i, (free i).value env = (params i).val) :
    eval E G (translateFormula p region bound free) env ↔ p.Eval values params := by
  induction p generalizing region free env with
  | verum => change (False → False) ↔ True; simp
  | falsum => exact Iff.rfl
  | rel r terms =>
    cases r with
    | eq => exact arithmeticAtom_eval D false terms bound free env values params bv fv
    | lt => exact arithmeticAtom_eval D true terms bound free env values params bv fv
  | nrel r terms =>
    cases r with
    | eq => exact not_congr (arithmeticAtom_eval D false terms bound free env values params bv fv)
    | lt => exact not_congr (arithmeticAtom_eval D true terms bound free env values params bv fv)
  | and p q ip iq => exact and_congr (ip _ _ _ _ values hw bv fv) (iq _ _ _ _ values hw bv fv)
  | or p q ip iq => exact or_congr (ip _ _ _ _ values hw bv fv) (iq _ _ _ _ values hw bv fv)
  | all p ih | exs p ih =>
    have changeEnv (x : D.Points) (i : Fin _) :
        (boundUnderBinder bound i).value (pushValue env x.val) =
        (Matrix.vecCons x values i).val := by
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa only [boundUnderBinder,Fin.cons_succ,Matrix.cons_val_succ,Function.comp_apply,Argument.up,Argument.value_shift]
          using bv j
    have same (x : D.Points) :=
      ih region.up (boundUnderBinder bound) (Argument.up ∘ free)
        (pushValue env x.val) (Matrix.vecCons x values) ((Argument.value_shift _ _ _).trans hw)
        (changeEnv x) (fun i => (Argument.value_shift _ _ _).trans (fv i))
    first
    | case all =>
        change (∀ x, E x (region.up.value (pushValue env x)) →
          eval E G (translateFormula p region.up (boundUnderBinder bound)
            (Argument.up ∘ free)) (pushValue env x)) ↔
          (∀ x : D.Points, p.Eval (Matrix.vecCons x values) params)
        simp only [Argument.up,Argument.value_shift,hw]
        exact ⟨fun h x => (same x).mp (h x.val x.property),fun h x hx => (same ⟨x,hx⟩).mpr (h ⟨x,hx⟩)⟩
    | case exs =>
        change (∃ x, E x (region.up.value (pushValue env x)) ∧
          eval E G (translateFormula p region.up (boundUnderBinder bound)
            (Argument.up ∘ free)) (pushValue env x)) ↔
          (∃ x : D.Points, p.Eval (Matrix.vecCons x values) params)
        simp only [Argument.up,Argument.value_shift,hw]
        exact ⟨fun ⟨x,hx,satisfies⟩ => ⟨⟨x,hx⟩,(same ⟨x,hx⟩).mp satisfies⟩,
          fun ⟨x,satisfies⟩ => ⟨x.val,x.property,(same x).mpr satisfies⟩⟩

end PalomarI3380.Logic.Expanded
