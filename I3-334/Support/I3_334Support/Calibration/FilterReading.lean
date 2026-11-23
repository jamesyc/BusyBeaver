module
public import I3_334Support.Calibration.NamedRepresentatives
public import I3_334Support.Arithmetic.OmegaReading
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder

def liftArguments {n : Nat} (args : Nat → ClosedSemiterm FilterLanguage n) :
    Nat → ClosedSemiterm FilterLanguage (n+1)
  | 0 => .bvar 0
  | i+1 => Rew.bShift (args i)

/-- Interpret membership on named points using algebra elements as their
representatives. The equality predicate is equality in the quotient. -/
def interpretMembership : {n : Nat} → Logic.Formula → (Nat → ClosedSemiterm FilterLanguage n) →
    Semisentence FilterLanguage n
  | _, .bot, _ => ⊥
  | _, .mem i j, args => membershipOp.operator ![args i,args j]
  | _, .eq i j, args => agreementOp.operator ![args i,args j]
  | _, .and p q, args => interpretMembership p args ⋏ interpretMembership q args
  | _, .or p q, args => interpretMembership p args ⋎ interpretMembership q args
  | _, .imp p q, args => interpretMembership p args 🡒 interpretMembership q args
  | _, .all p, args => .all (namedPointOp.operator ![.bvar 0] 🡒 interpretMembership p (liftArguments args))
  | _, .ex p, args => .exs (namedPointOp.operator ![.bvar 0] ⋏ interpretMembership p (liftArguments args))

def interpretSentence (p : Logic.Formula) : FFL.FirstOrder.Sentence FilterLanguage :=
  interpretMembership p (fun _ => unitOp.term)

section Meaning

variable {A : Type} [Tarski.Structure FilterLanguage A] [Tarski.Structure.Eq FilterLanguage A]
variable (C : FilterModel A)

private theorem operator_app {n k : Nat} (form : Semiformula.Operator FilterLanguage k)
    (terms : Fin k → ClosedSemiterm FilterLanguage n) (env : Fin n → A) :
    (form.operator terms).Evalb env ↔ form.sentence.Evalb (fun i => (terms i).valb env) := by
  simp [Semiformula.Operator.operator,Semiformula.eval_rew,Semiterm.val_rew,
    Semiterm.valb,Function.comp_def,Empty.eq_elim]

private theorem pair_of_values {n : Nat} (left right : ClosedSemiterm FilterLanguage n)
    (env : Fin n → A) {x y : A} (hx : left.valb env = x) (hy : right.valb env = y) :
    (fun i => (![left,right] i).valb env) = ![x,y] := by
  funext i
  refine Fin.cases hx (fun j => ?_) i
  have zero : j = 0 := Subsingleton.elim _ _
  subst j
  exact hy

theorem interpretMembership_eval {n : Nat} (p : Logic.Formula) (bound : Logic.Bound p n)
    (args : Nat → ClosedSemiterm FilterLanguage n) (env : Fin n → A)
    (representatives : Nat → C.Representative)
    (values : ∀ i, i < n → (args i).valb env = (representatives i).val.val) :
    (interpretMembership p args).Evalb env ↔ Logic.eval C.mem p (fun i => C.asPoint (representatives i)) := by
  induction p generalizing n args env representatives with
  | bot => rfl
  | mem i j =>
    have same := pair_of_values (args i) (args j) env (values i bound.1) (values j bound.2)
    refine (operator_app ..).trans ?_
    rw [same]
    exact C.matches_membership _ _
  | eq i j =>
    have same := pair_of_values (args i) (args j) env (values i bound.1) (values j bound.2)
    refine (operator_app ..).trans ?_
    rw [same]
    exact C.matches_equality _ _
  | and p q ip iq =>
    exact and_congr (ip bound.1 args env representatives values) (iq bound.2 args env representatives values)
  | or p q ip iq =>
    exact or_congr (ip bound.1 args env representatives values) (iq bound.2 args env representatives values)
  | imp p q ip iq =>
    rw [interpretMembership,LogicalConnective.HomClass.map_imply]
    exact imp_congr (ip bound.1 args env representatives values) (iq bound.2 args env representatives values)
  | all p ih | ex p ih =>
    have named (x : A) : (namedPointOp.operator ![.bvar 0]).Evalb (x :> env) ↔
        ∃ r : C.Representative, r.val.val = x := by
      refine (operator_app ..).trans ?_
      have same : (fun i : Fin 1 => ((![.bvar 0] i : ClosedSemiterm FilterLanguage (n+1))).valb (x :> env)) =
          ![x] := funext fun i => by
        have only : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      rw [same]
      exact C.representative_eval x
    have inside (r : C.Representative) :
        (interpretMembership p (liftArguments args)).Evalb (r.val.val :> env) ↔
          Logic.eval C.mem p (Logic.pushValue (fun i => C.asPoint (representatives i)) (C.asPoint r)) := by
      have compatible :
          (fun i => C.asPoint (Logic.pushValue representatives r i)) =
            Logic.pushValue (fun i => C.asPoint (representatives i)) (C.asPoint r) :=
        funext fun i => by cases i <;> rfl
      rw [← compatible]
      apply ih bound _ _ _
      intro i hi
      cases i with
      | zero => rfl
      | succ i =>
        have inside : i < n := by omega
        simpa only [liftArguments,Logic.pushValue,Semiterm.valb,Semiterm.val_bShift] using values i inside
    first
    | case all =>
        change (∀ x, ((namedPointOp.operator ![.bvar 0] 🡒
          interpretMembership p (liftArguments args))).Evalb (x :> env)) ↔
          ∀ q, Logic.eval C.mem p (Logic.pushValue (fun i => C.asPoint (representatives i)) q)
        simp only [LogicalConnective.HomClass.map_imply]
        constructor
        · intro h q
          obtain ⟨r,rfl⟩ := C.asPoint_onto q
          exact (inside r).mp (h _ ((named _).mpr ⟨r,rfl⟩))
        · intro h x isNamed
          obtain ⟨r,rfl⟩ := (named x).mp isNamed
          exact (inside r).mpr (h (C.asPoint r))
    | case ex =>
        change (∃ x, (namedPointOp.operator ![.bvar 0]).Evalb (x :> env) ∧
          (interpretMembership p (liftArguments args)).Evalb (x :> env)) ↔
          ∃ q, Logic.eval C.mem p (Logic.pushValue (fun i => C.asPoint (representatives i)) q)
        constructor
        · rintro ⟨x,isNamed,h⟩
          obtain ⟨r,rfl⟩ := (named x).mp isNamed
          exact ⟨C.asPoint r,(inside r).mp h⟩
        · rintro ⟨q,h⟩
          obtain ⟨r,rfl⟩ := C.asPoint_onto q
          exact ⟨r.val.val,(named _).mpr ⟨r,rfl⟩,(inside r).mpr h⟩

theorem interpretSentence_eval [Nonempty A] (p : Logic.Formula) (closed : Logic.Closed p)
    (env : Nat → C.Domain) :
    A↓[FilterLanguage] ⊧ interpretSentence p ↔ Logic.eval C.mem p env := by
  classical
  let representatives := fun i => Classical.choose (C.asPoint_onto (env i))
  have eq : (fun i => C.asPoint (representatives i)) = env :=
    funext fun i => Classical.choose_spec (C.asPoint_onto (env i))
  rw [← eq]
  exact interpretMembership_eval C p closed _ ![] representatives (fun i h => by omega)

end Meaning
end PalomarI3380.Calibration
