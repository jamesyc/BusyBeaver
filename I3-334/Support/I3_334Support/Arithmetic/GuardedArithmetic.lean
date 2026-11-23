module
public import I3_334Support.Arithmetic.OmegaReading
@[expose] public section

namespace PalomarI3380.Logic.Expanded

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}

def allNaturalArguments (omega : V) : Nat → Formula V
  | 0 => .imp .bot .bot
  | n+1 => .and (allNaturalArguments omega n) (.mem (.variable n) (.named omega))

theorem allNaturalArguments_scope (omega : V) (n : Nat) : Bound (allNaturalArguments omega n) n := by
  induction n with
  | zero => exact ⟨trivial,trivial⟩
  | succ n ih => exact ⟨bound_extension ih (Nat.le_succ n),Nat.lt_succ_self n,trivial⟩

theorem allNaturalArguments_eval (omega : V) (n : Nat) (env : Nat → V) :
    eval E G (allNaturalArguments omega n) env ↔ ∀ i < n, E (env i) omega := by
  induction n with
  | zero => simp [allNaturalArguments,eval]
  | succ n ih =>
    simp only [allNaturalArguments,eval,ih,Argument.value]
    constructor
    · rintro ⟨previous,last⟩ i range
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ range) with h | rfl
      · exact previous i h
      · exact last
    · intro all
      exact ⟨fun i hi => all i (Nat.lt_trans hi (Nat.lt_succ_self n)),
        all n (Nat.lt_succ_self n)⟩

variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

def guardedArithmetic {ξ : Type} {n : Nat} (φ : Semiformula ℒₒᵣ ξ n) (params : ξ → D.Points) :
    Formula V :=
  .and (allNaturalArguments D.omega n)
    (translateFormula φ (.named D.omega) (fun i => .variable i.val) (fun j => .named (params j).val))

theorem guardedArithmetic_scope {ξ : Type} {n : Nat} (φ : Semiformula ℒₒᵣ ξ n) (params : ξ → D.Points) :
    Bound (guardedArithmetic D φ params) n :=
  ⟨allNaturalArguments_scope D.omega n,translateFormula_scope φ trivial (fun i => i.isLt) (fun _ => trivial)⟩

/-- Arithmetic syntax gives a membership predicate on the actual
model's natural numbers, with parameters and an explicit domain guard. -/
theorem guardedArithmetic_eval {ξ : Type} {n : Nat} (φ : Semiformula ℒₒᵣ ξ n)
    (params : ξ → D.Points) (env : Nat → V) :
    eval E G (guardedArithmetic D φ params) env ↔
      ∃ v : Fin n → D.Points, (∀ i, (v i).val = env i.val) ∧ φ.Eval v params := by
  unfold guardedArithmetic
  constructor
  · rintro ⟨all,holds⟩
    let v := fun i : Fin n => (⟨env i.val,(allNaturalArguments_eval D.omega n env).mp all i.val i.isLt⟩ : D.Points)
    refine ⟨v,fun _ => rfl,?_⟩
    exact (translateFormula_eval D φ (.named D.omega)
      (fun i => .variable i.val) (fun j => .named (params j).val) env v params rfl
      (fun _ => rfl) (fun _ => rfl)).mp holds
  · rintro ⟨v,same,holds⟩
    refine ⟨(allNaturalArguments_eval D.omega n env).mpr ?_,
      (translateFormula_eval D φ (.named D.omega)
      (fun i => .variable i.val) (fun j => .named (params j).val) env v params rfl
        (fun i => (same i).symm) (fun _ => rfl)).mpr holds⟩
    intro i hi
    exact same ⟨i,hi⟩ ▸ (v ⟨i,hi⟩).property

theorem OmegaDomain.separate_arithmetic {ξ : Type} (p : Semiformula ℒₒᵣ ξ 1) (params : ξ → D.Points) :
    ∃ subset : V, ∀ x, E x subset ↔ ∃ n : D.Points, n.val = x ∧ p.Eval ![n] params := by
  let form := guardedArithmetic D p params
  let pred := fun (x _ : V) => eval E G form (fun _ => x)
  have scope := guardedArithmetic_scope D p params
  have named : Binary E G pred :=
    ⟨form,bound_extension scope (by decide),fun env => eval_congr E G form scope
      (fun i hi => by
        have eq : i=0 := by omega
        rw [eq])⟩
  obtain ⟨subset,meaning⟩ := L.separation pred named D.omega (Classical.choice inhabited)
  refine ⟨subset,fun x => (meaning x).trans ?_⟩
  change E x D.omega ∧ eval E G form (fun _ => x) ↔ _
  rw [guardedArithmetic_eval]
  constructor
  · rintro ⟨_,v,same,truth⟩
    refine ⟨v 0,same 0,?_⟩
    have vector : v = ![v 0] := Matrix.fun_eq_vec_one v
    rwa [← vector]
  · rintro ⟨n,represent,truth⟩
    refine ⟨represent ▸ n.property,![n],?_ ,truth⟩
    intro i
    have zero : i = 0 := Subsingleton.elim _ _
    simpa only [zero,Matrix.cons_val_zero] using represent

theorem arithmeticBinary {ξ : Type} (p : Semiformula ℒₒᵣ ξ 2) (params : ξ → D.Points) :
    Binary E G (fun x y => ∃ a b : D.Points, a.val = x ∧ b.val = y ∧ p.Eval ![a,b] params) := by
  refine ⟨guardedArithmetic D p params,guardedArithmetic_scope D p params,fun env => ?_⟩
  rw [guardedArithmetic_eval D p params env]
  constructor
  · rintro ⟨v,same,truth⟩
    refine ⟨v 0,v 1,same 0,same 1,?_⟩
    rwa [← Matrix.fun_eq_vec_two v]
  · rintro ⟨a,b,x,y,truth⟩
    refine ⟨![a,b],?_ ,truth⟩
    intro i
    refine Fin.cases x (fun j => ?_) i
    have zero : j=0 := Subsingleton.elim _ _
    subst j
    exact y

end PalomarI3380.Logic.Expanded
