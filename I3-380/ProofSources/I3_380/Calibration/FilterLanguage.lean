module
public import I3_380.Equations
public import Foundation.FirstOrder.Arithmetic.Basic.Model
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder

/-- The native operations together with a predicate on subidentities.
The language keeps first-order equality as an explicit relation. -/
inductive FunctionSymbol : Nat → Type where
  | constant : Constant → FunctionSymbol 0
  | complement : FunctionSymbol 1
  | converse : FunctionSymbol 1
  | choose : FunctionSymbol 1
  | localRelation : FunctionSymbol 1
  | nand : FunctionSymbol 2
  | product : FunctionSymbol 2
  | node : FunctionSymbol 3
  deriving DecidableEq

inductive RelationSymbol : Nat → Type where
  | chosen : RelationSymbol 1
  | equal : RelationSymbol 2
  deriving DecidableEq

def FilterLanguage : Language := ⟨FunctionSymbol,RelationSymbol⟩

instance : FilterLanguage.Eq := ⟨RelationSymbol.equal⟩

def algebraOf (V : Type) [Tarski.Structure FilterLanguage V] : Algebra V where
  constant c := Tarski.Structure.func (L := FilterLanguage) (FunctionSymbol.constant c : FilterLanguage.Func 0) ![]
  neg x := Tarski.Structure.func (L := FilterLanguage) (FunctionSymbol.complement : FilterLanguage.Func 1) ![x]
  converse x := Tarski.Structure.func (L := FilterLanguage) (FunctionSymbol.converse : FilterLanguage.Func 1) ![x]
  choice x := Tarski.Structure.func (L := FilterLanguage) (FunctionSymbol.choose : FilterLanguage.Func 1) ![x]
  localRel x := Tarski.Structure.func (L := FilterLanguage) (FunctionSymbol.localRelation : FilterLanguage.Func 1) ![x]
  nand x y := Tarski.Structure.func (L := FilterLanguage) (FunctionSymbol.nand : FilterLanguage.Func 2) ![x,y]
  product x y := Tarski.Structure.func (L := FilterLanguage) (FunctionSymbol.product : FilterLanguage.Func 2) ![x,y]
  node x y z := Tarski.Structure.func (L := FilterLanguage) (FunctionSymbol.node : FilterLanguage.Func 3) ![x,y,z]

def chosenOf (V : Type) [Tarski.Structure FilterLanguage V] (x : V) : Prop :=
  Tarski.Structure.rel (L := FilterLanguage) (RelationSymbol.chosen : FilterLanguage.Rel 1) ![x]

@[instance_reducible] def structureOf {V : Type} (M : Algebra V) (chosen : V → Prop) : Tarski.Structure FilterLanguage V where
  func {k} symbol values := match (show FunctionSymbol k from symbol) with
    | .constant c => M.constant c
    | .complement => M.neg (values 0)
    | .converse => M.converse (values 0)
    | .choose => M.choice (values 0)
    | .localRelation => M.localRel (values 0)
    | .nand => M.nand (values 0) (values 1)
    | .product => M.product (values 0) (values 1)
    | .node => M.node (values 0) (values 1) (values 2)
  rel {k} symbol values := match (show RelationSymbol k from symbol) with
    | .equal => values 0 = values 1
    | .chosen => chosen (values 0)

theorem algebra_structureOf {V : Type} (M : Algebra V) (chosen : V → Prop) :
    @algebraOf V (structureOf M chosen) = M := by
  cases M
  rfl

variable {X : Type} {n : Nat}

def embedTerm (names : X → Semiterm FilterLanguage Empty n) :
    Term X → Semiterm FilterLanguage Empty n
  | .var x => names x
  | .const c => .func (FunctionSymbol.constant c) ![]
  | .neg t => .func FunctionSymbol.complement ![embedTerm names t]
  | .converse t => .func FunctionSymbol.converse ![embedTerm names t]
  | .choice t => .func FunctionSymbol.choose ![embedTerm names t]
  | .localRel t => .func FunctionSymbol.localRelation ![embedTerm names t]
  | .nand a b => .func FunctionSymbol.nand ![embedTerm names a,embedTerm names b]
  | .product a b => .func FunctionSymbol.product ![embedTerm names a,embedTerm names b]
  | .node a b c => .func FunctionSymbol.node ![embedTerm names a,embedTerm names b,embedTerm names c]

theorem symbol_value {V : Type} [Tarski.Structure FilterLanguage V]
    {k : Nat} (symbol : FunctionSymbol k) (args : Fin k → Semiterm FilterLanguage Empty n)
    (bounds : Fin n → V) :
    (Semiterm.func (L := FilterLanguage) symbol args).valb bounds =
      Tarski.Structure.func (L := FilterLanguage) symbol ((Semiterm.valb bounds) ∘ args) := rfl

theorem embedTerm_eval {V : Type} [Tarski.Structure FilterLanguage V]
    (names : X → Semiterm FilterLanguage Empty n)
    (bounds : Fin n → V) (term : Term X) :
    (embedTerm names term).valb bounds =
      (algebraOf V).eval (fun v => (names v).valb bounds) term := by
  induction term <;>
    simp [embedTerm,algebraOf,Algebra.eval,symbol_value,Matrix.comp_vecCons',
      Matrix.empty_eq,Matrix.constant_eq_singleton,Function.comp_def, *]

def equationSentence (e : Equation) : FFL.FirstOrder.Sentence FilterLanguage :=
  ∀¹* ((Semiformula.Operator.Eq.eq (L := FilterLanguage)).operator ![embedTerm (fun i => .bvar i) e.1,
    embedTerm (fun i => .bvar i) e.2])

theorem equationSentence_eval {V : Type} [Nonempty V] [Tarski.Structure FilterLanguage V]
    [Tarski.Structure.Eq FilterLanguage V] (e : Equation) :
    V↓[FilterLanguage] ⊧ equationSentence e ↔ (algebraOf V).Satisfies e := by
  simp [equationSentence,models_iff,Semiformula.eval_allClosure,Algebra.Satisfies,
    Tarski.Structure.eq_iff_eq,embedTerm_eval]

end PalomarI3380.Calibration
