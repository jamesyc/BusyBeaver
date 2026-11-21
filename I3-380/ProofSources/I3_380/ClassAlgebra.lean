module
public import I3_380.Logic.ExpandedSubstitution
public import I3_380.Logic.ModelOperations
public import I3_380.Definable
@[expose] public section

namespace PalomarI3380.Logic.Expanded

variable {V : Type} {E G : V → V → Prop}

/-- Relations are identified extensionally. Their first-order definitions
are evidence of membership in the carrier, with no syntactic labels
retained in the equality of algebra elements. -/
structure ClassRelation (E G : V → V → Prop) where
  holds : V → V → Prop
  definable : Binary E G holds

namespace ClassRelation

theorem ext {p q : ClassRelation E G} (equal : ∀ x y, p.holds x y ↔ q.holds x y) : p = q := by
  have same : p.holds = q.holds := funext fun x => funext fun y => propext (equal x y)
  cases p
  cases q
  cases same
  rfl

def one : ClassRelation E G := ⟨Eq,Binary.equality⟩
def top : ClassRelation E G := ⟨fun _ _ => True,Binary.universal⟩
def member : ClassRelation E G := ⟨E,Binary.membership⟩
def subset : ClassRelation E G :=
  ⟨fun a b => ∀ x, E x a → E x b,
    ⟨.all (.imp (.mem (.variable 0) (.variable 1)) (.mem (.variable 0) (.variable 2))),
      by simp [Bound,Argument.bound], fun _ => Iff.rfl⟩⟩

def complement (r : ClassRelation E G) : ClassRelation E G :=
  ⟨fun x y => ¬r.holds x y,r.definable.complement⟩

def converse (r : ClassRelation E G) : ClassRelation E G :=
  ⟨fun x y => r.holds y x,r.definable.converse⟩

def nand (r s : ClassRelation E G) : ClassRelation E G :=
  ⟨fun x y => ¬(r.holds x y ∧ s.holds x y),(r.definable.intersection s.definable).complement⟩

def product (r s : ClassRelation E G) : ClassRelation E G :=
  ⟨fun x y => ∃ z, r.holds x z ∧ s.holds z y,r.definable.product s.definable⟩

def formulaArguments (a b : Argument V) (i : Nat) : Argument V :=
  if i = 0 then a else b

noncomputable def formula (r : ClassRelation E G) : Formula V :=
  Classical.choose r.definable

theorem formula_scope (r : ClassRelation E G) : Bound r.formula 2 :=
  (Classical.choose_spec r.definable).1

theorem formula_eval (r : ClassRelation E G) (env : Nat → V) :
    eval E G r.formula env ↔ r.holds (env 0) (env 1) :=
  (Classical.choose_spec r.definable).2 env

noncomputable def reference (r : ClassRelation E G) (a b : Argument V) : Formula V :=
  r.formula.substitute (formulaArguments a b)

theorem reference_bound (r : ClassRelation E G) {a b : Argument V} {n : Nat}
    (ha : a.bound n) (hb : b.bound n) : Bound (r.reference a b) n :=
  substitute_bound r.formula r.formula_scope fun i _ => by
    simp only [formulaArguments]
    split <;> assumption

theorem reference_eval (r : ClassRelation E G) (a b : Argument V) (env : Nat → V) :
    eval E G (r.reference a b) env ↔ r.holds (a.value env) (b.value env) :=
  (eval_substitute E G r.formula (formulaArguments a b) env).trans (r.formula_eval _)

def algebra (E G : V → V → Prop) : Algebra (ClassRelation E G) where
  constant
    | .I => one
    | .E => member
    | .T => subset
    | _ => top
  neg := complement
  converse := converse
  nand := nand
  product := product
  choice := id
  localRel := id
  node x _ _ := x

def square (E G : V → V → Prop) : SquareRepresentation (algebra E G) V where
  rel := ClassRelation.holds
  complement _ _ _ := Iff.rfl
  converse _ _ _ := Iff.rfl
  nand _ _ _ _ := Iff.rfl
  product _ _ _ _ := Iff.rfl
  universal _ _ := Iff.rfl
  identity _ _ := Iff.rfl

open SquareRepresentation in
noncomputable def compile : RelationFormula (ClassRelation E G) → Formula V
  | .bot => .bot
  | .eq i j => .eq (.variable i) (.variable j)
  | .atom r i j => r.reference (.variable i) (.variable j)
  | .and p q => .and (compile p) (compile q)
  | .or p q => .or (compile p) (compile q)
  | .imp p q => .imp (compile p) (compile q)
  | .all p => .all (compile p)
  | .ex p => .ex (compile p)

open SquareRepresentation in
theorem compile_scope (p : RelationFormula (ClassRelation E G)) {n : Nat} (h : p.Bound n) :
    Bound (compile p) n := by
  induction p generalizing n with
  | bot => trivial
  | eq _ _ => exact h
  | atom r _ _ => exact r.reference_bound h.1 h.2
  | and p q ip iq | or p q ip iq | imp p q ip iq => exact ⟨ip h.1,iq h.2⟩
  | all p ih | ex p ih => exact ih h

open SquareRepresentation in
theorem compile_eval (p : RelationFormula (ClassRelation E G)) (env : Nat → V) :
    eval E G (compile p) env ↔ RelationFormula.eval (square E G) p env := by
  induction p generalizing env with
  | bot | eq => rfl
  | atom r i j => exact r.reference_eval (.variable i) (.variable j) env
  | and p q ip iq => exact and_congr (ip env) (iq env)
  | or p q ip iq => exact or_congr (ip env) (iq env)
  | imp p q ip iq => exact imp_congr (ip env) (iq env)
  | all p ih => exact forall_congr' fun x => ih (pushValue env x)
  | ex p ih => exact exists_congr fun x => ih (pushValue env x)

open SquareRepresentation in
theorem binary_class (p : RelationFormula (ClassRelation E G)) (params : List V) (default : V)
    (bound : p.Bound (params.length + 2)) :
    Binary E G (fun x y => RelationFormula.eval (square E G) p (parameterEnv params x y)) := by
  let index : Nat → Argument V
    | 0 => .variable 0
    | 1 => .variable 1
    | i + 2 => .named (params[i]?.getD default)
  have inside : ∀ i, i < params.length + 2 → (index i).bound 2 := by
    intro i _
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i =>
      cases i with
      | zero => exact Nat.succ_lt_succ (Nat.zero_lt_succ _)
      | succ i => trivial
  refine ⟨(compile p).substitute index, substitute_bound _ (compile_scope p bound) inside, fun env => ?_⟩
  refine (eval_substitute E G (compile p) index env).trans ((eval_congr E G (compile p)
    (compile_scope p bound) ?_).trans (compile_eval p (parameterEnv params (env 0) (env 1))))
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      have idx : i < params.length := by omega
      change params[i]?.getD default = params[i]?.getD (env 0)
      rw [List.getElem?_eq_getElem idx]
      rfl

end ClassRelation
end PalomarI3380.Logic.Expanded
