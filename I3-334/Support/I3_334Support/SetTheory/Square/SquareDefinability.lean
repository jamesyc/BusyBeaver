module
public import I3_334Support.SetTheory.Square.SquareTuples
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open PalomarI3380.Logic (pushValue)

/-- First-order syntax with equality and any fixed represented binary
relations as extra predicates. -/
inductive RelationFormula (A : Type) where
  | bot
  | eq (i j : Nat)
  | atom (label : A) (i j : Nat)
  | and (left right : RelationFormula A)
  | or (left right : RelationFormula A)
  | imp (left right : RelationFormula A)
  | all (body : RelationFormula A)
  | ex (body : RelationFormula A)

namespace RelationFormula

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}

def Bound {A : Type} : RelationFormula A → Nat → Prop
  | .bot, _ => True
  | .eq i j, n | .atom _ i j, n => i < n ∧ j < n
  | .and p q, n | .or p q, n | .imp p q, n => p.Bound n ∧ q.Bound n
  | .all p, n | .ex p, n => p.Bound (n + 1)

def eval (S : SquareRepresentation M Point) : RelationFormula A → (Nat → Point) → Prop
  | .bot, _ => False
  | .eq i j, env => env i = env j
  | .atom a i j, env => S.rel a (env i) (env j)
  | .and p q, env => eval S p env ∧ eval S q env
  | .or p q, env => eval S p env ∨ eval S q env
  | .imp p q, env => eval S p env → eval S q env
  | .all p, env => ∀ x, eval S p (pushValue env x)
  | .ex p, env => ∃ x, eval S p (pushValue env x)

def liftMembership (member : A) : Logic.Formula → RelationFormula A
  | .bot => .bot
  | .eq i j => .eq i j
  | .mem i j => .atom member i j
  | .and p q => .and (liftMembership member p) (liftMembership member q)
  | .or p q => .or (liftMembership member p) (liftMembership member q)
  | .imp p q => .imp (liftMembership member p) (liftMembership member q)
  | .all p => .all (liftMembership member p)
  | .ex p => .ex (liftMembership member p)

theorem liftMembership_bound (member : A) (p : Logic.Formula) (n : Nat) :
    (liftMembership member p).Bound n ↔ Logic.Bound p n := by
  induction p generalizing n <;> simp only [liftMembership, Bound, Logic.Bound, *]

theorem liftMembership_eval (member : A) (p : Logic.Formula) (env : Nat → Point) :
    eval S (liftMembership member p) env ↔ Logic.eval (S.rel member) p env := by
  induction p generalizing env <;> simp only [liftMembership, eval, Logic.eval, *]

private theorem push_agreement {n : Nat} {env other : Nat → Point}
    (same : ∀ i, i < n → env i = other i) (x : Point) (i : Nat) (hi : i < n + 1) :
    pushValue env x i = pushValue other x i := by
  cases i with
  | zero => rfl
  | succ i => exact same i (by omega)

theorem eval_congr (p : RelationFormula A) {n : Nat} (hn : p.Bound n) (env other : Nat → Point)
    (same : ∀ i, i < n → env i = other i) : eval S p env ↔ eval S p other := by
  induction p generalizing n env other with
  | bot => exact Iff.rfl
  | eq i j => simp only [eval, same i hn.1, same j hn.2]
  | atom a i j => simp only [eval, same i hn.1, same j hn.2]
  | and p q ihP ihQ => exact and_congr (ihP hn.1 _ _ same) (ihQ hn.2 _ _ same)
  | or p q ihP ihQ => exact or_congr (ihP hn.1 _ _ same) (ihQ hn.2 _ _ same)
  | imp p q ihP ihQ => exact imp_congr (ihP hn.1 _ _ same) (ihQ hn.2 _ _ same)
  | all p ih =>
    exact forall_congr' fun x => ih hn _ _ (push_agreement same x)
  | ex p ih =>
    exact exists_congr fun x => ih hn _ _ (push_agreement same x)

/-- A truth diagonal for the formula, restricted to codes of valid
assignments. Extra relation atoms are interpreted by their algebra elements. -/
def truth (P : QuasiProjections S) (n : Nat) : RelationFormula A → A
  | .bot => P.within n (M.neg (M.constant .U))
  | .eq i j => P.within n (M.product (P.projection i) (M.converse (P.projection j)))
  | .atom a i j =>
    P.within n (M.product (M.product (P.projection i) a) (M.converse (P.projection j)))
  | .and p q => P.within n (M.inf (truth P n p) (truth P n q))
  | .or p q => P.within n (join M (truth P n p) (truth P n q))
  | .imp p q => P.within n (join M (M.neg (truth P n p)) (truth P n q))
  | .ex p => P.within n (P.project (truth P (n + 1) p))
  | .all p => P.within n (M.neg (P.project (P.within (n + 1) (M.neg (truth P (n + 1) p)))))

theorem truth_domain (P : QuasiProjections S) (n : Nat) (p : RelationFormula A) {x y : Point}
    (h : S.rel (truth P n p) x y) : S.rel (P.tupleDomain n) x y := by
  cases p <;> exact (P.within_rel.mp h).1

/-- Evaluate a first-order formula by the constructed algebra element. -/
theorem truth_correct (P : QuasiProjections S) (p : RelationFormula A)
    {n : Nat} {code : Point} {env : Nat → Point} (hn : p.Bound n) (enc : P.Encodes n code env) :
    S.rel (truth P n p) code code ↔ eval S p env := by
  classical
  induction p generalizing n code env with
  | bot => simp only [truth, P.within_code enc, S.complement, S.universal, eval, not_true_eq_false]
  | eq i j =>
    simp only [truth, P.within_code enc, S.product, S.converse, P.projection_value enc hn.1,
      P.projection_value enc hn.2, eval]
    constructor
    · rintro ⟨_, e₁, e₂⟩
      exact e₁.symm.trans e₂
    · intro h
      exact ⟨env i, rfl, h⟩
  | atom a i j =>
    simp only [truth, P.within_code enc, S.product, S.converse, P.projection_value enc hn.1,
      P.projection_value enc hn.2, eval]
    constructor
    · rintro ⟨_, ⟨_, rfl, edge⟩, rfl⟩
      exact edge
    · intro edge
      exact ⟨env j, ⟨env i, rfl, edge⟩, rfl⟩
  | and p q ihP ihQ =>
    have meetEq : S.rel (M.inf (truth P n p) (truth P n q)) code code ↔ _ :=
      S.meet _ _ _ _
    simp only [truth, P.within_code enc, meetEq, ihP hn.1 enc, ihQ hn.2 enc, eval]
  | or p q ihP ihQ =>
    simp only [truth, P.within_code enc, S.join_iff, ihP hn.1 enc, ihQ hn.2 enc, eval]
  | imp p q ihP ihQ =>
    simp only [truth, P.within_code enc, S.join_iff, S.complement, ihP hn.1 enc, ihQ hn.2 enc, eval]
    by_cases hp : eval S p env <;> simp [hp]
  | ex p ih =>
    simp only [truth, P.within_code enc, eval]
    exact P.project_at enc (fun _ _ => truth_domain P _ _) (eval S p)
      (fun _ _ h => ih hn h)
  | all p ih =>
    simp only [truth, P.within_code enc, S.complement, eval]
    have hasCounterexample : S.rel (P.project (P.within (n + 1) (M.neg (truth P (n + 1) p)))) code code ↔
        ∃ x, ¬eval S p (pushValue env x) :=
      P.project_at enc (fun _ _ h => (P.within_rel.mp h).1) (fun s => ¬eval S p s)
        (fun _ _ e => by rw [P.within_code e, S.complement, ih hn e])
    rw [hasCounterexample]
    exact ⟨fun h x => Classical.byContradiction fun neg => h ⟨x, neg⟩,
      fun h ⟨x, neg⟩ => neg (h x)⟩

end RelationFormula
end PalomarI3380.SquareRepresentation
