module
public import I3_380.Calibration.RelationalLanguage
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder

/-- Evaluate argument graphs in a shared block of existential variables. -/
def argumentGraphs {n m k : Nat} (terms : Fin k → Semisentence GraphLanguage (n+1))
    (inherited : Fin n → Fin (m+k)) : Semisentence GraphLanguage (m+k) :=
  Matrix.conj fun i => (terms i) ⇜
    (.bvar (i.addCast m) :> fun j => .bvar (inherited j))

def termGraph {n : Nat} : ClosedSemiterm FilterLanguage n → Semisentence GraphLanguage (n+1)
  | .bvar i =>
    .rel (.relation .equal) ![.bvar 0,.bvar i.succ]
  | .fvar impossible => impossible.elim
  | .func (arity := k) symbol args =>
    ∃¹^[k] (argumentGraphs (fun i => termGraph (args i)) (fun j => j.succ.addNat k) ⋏
      .rel (.operation symbol) (.bvar ((0 : Fin (n+1)).addNat k) :> fun i => .bvar (i.addCast (n+1))))

def graphAtom {n k : Nat} (symbol : RelationSymbol k) (args : Fin k → ClosedSemiterm FilterLanguage n) :
    Semisentence GraphLanguage n :=
  ∃¹^[k] (argumentGraphs (fun i => termGraph (args i)) (fun j => j.addNat k) ⋏
    .rel (.relation symbol) (fun i => .bvar (i.addCast n)))

/-- Relationalize an ordinary filter formula through the operation graphs. -/
def graphFormula : {n : Nat} → Semisentence FilterLanguage n → Semisentence GraphLanguage n
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, .rel symbol args => graphAtom symbol args
  | _, .nrel symbol args => ∼graphAtom symbol args
  | _, .and a b => .and (graphFormula a) (graphFormula b)
  | _, .or a b => .or (graphFormula a) (graphFormula b)
  | _, .all a => .all (graphFormula a)
  | _, .exs a => .exs (graphFormula a)

section Semantics

variable {A : Type} [Tarski.Structure FilterLanguage A] [Tarski.Structure.Eq FilterLanguage A]
local instance : Tarski.Structure GraphLanguage A := graphStructure

private theorem eval_graph_rel {n k : Nat} (symbol : GraphSymbol k)
    (args : Fin k → ClosedSemiterm GraphLanguage n) (env : Fin n → A) :
    (Semiformula.rel (L := GraphLanguage) symbol args).Evalb env ↔
      Tarski.Structure.rel (L := GraphLanguage) symbol (fun i => (args i).valb env) := Iff.rfl

private theorem eval_conj {k n : Nat} (p : Fin k → Semisentence GraphLanguage n) (env : Fin n → A) :
    (Matrix.conj p).Evalb env ↔ ∀ i, (p i).Evalb env := by
  induction k with
  | zero => simp
  | succ k ih =>
    change ((p 0).Evalb env ∧ (Matrix.conj (Matrix.vecTail p)).Evalb env) ↔ _
    simp [ih,Fin.forall_fin_succ,Matrix.vecTail]

theorem argumentGraphs_eval {n m k : Nat} (terms : Fin k → Semisentence GraphLanguage (n+1))
    (inherited : Fin n → Fin (m+k)) (v : Fin (m+k) → A) :
    (argumentGraphs terms inherited).Evalb v ↔
      ∀ i, (terms i).Evalb (v (i.addCast m) :> fun j => v (inherited j)) := by
  rw [argumentGraphs,eval_conj]
  apply forall_congr'
  intro i
  rw [Semiformula.eval_substs]
  have assignment : Semiterm.val v Empty.elim ∘
      (.bvar (i.addCast m) :> fun j => (.bvar (inherited j) : ClosedSemiterm GraphLanguage (m+k))) =
      (v (i.addCast m) :> fun j => v (inherited j)) := by
    funext j
    cases j using Fin.cases <;> rfl
  rw [assignment]

theorem termGraph_eval {n : Nat} (t : ClosedSemiterm FilterLanguage n)
    (out : A) (env : Fin n → A) :
    (termGraph t).Evalb (out :> env) ↔ out = t.valb env := by
  induction t generalizing out with
  | bvar i =>
    rw [termGraph,eval_graph_rel]
    have assignment : (fun j : Fin 2 =>
        (![.bvar 0,.bvar i.succ] j : ClosedSemiterm GraphLanguage (n+1)).valb (out :> env)) =
        ![out,env i] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      have zero : k = 0 := Subsingleton.elim _ _
      subst k
      rfl
    rw [assignment]
    exact Tarski.Structure.Eq.eq (L := FilterLanguage) out (env i)
  | fvar impossible => exact impossible.elim
  | @func k symbol args ih =>
    simp only [termGraph,Semiformula.eval_exsItr,LogicalConnective.HomClass.map_and,argumentGraphs_eval,
      eval_graph_rel,Semiterm.val,Matrix.appeendr_addCast,Matrix.appeendr_addNat,
      Matrix.cons_val_zero,Matrix.cons_val_succ,ih]
    have assignment (values : Fin k → A) :
        (fun i : Fin (k+1) =>
          ((.bvar ((0 : Fin (n+1)).addNat k) :> fun j => .bvar (j.addCast (n+1))) i :
            ClosedSemiterm GraphLanguage (n+1+k)).valb (Matrix.appendr values (out :> env))) =
          (out :> values) := by
      funext i
      cases i using Fin.cases with
      | zero => simp [Semiterm.valb,Semiterm.val]
      | succ i => simp [Semiterm.valb,Semiterm.val]
    simp only [assignment]
    change (∃ values : Fin k → A,
      (∀ i, values i = (args i).valb env) ∧
      out = Tarski.Structure.func (L := FilterLanguage) symbol values) ↔ _
    constructor
    · rintro ⟨values,equal,output⟩
      rw [show values = (fun i => (args i).valb env) from funext equal] at output
      exact output
    · intro output
      exact ⟨_,fun _ => rfl,output⟩

theorem graphAtom_eval {n k : Nat} (symbol : RelationSymbol k) (args : Fin k → ClosedSemiterm FilterLanguage n)
    (env : Fin n → A) :
    (graphAtom symbol args).Evalb env ↔
      (Semiformula.rel (L := FilterLanguage) symbol args).Evalb env := by
  simp only [graphAtom,Semiformula.eval_exsItr,LogicalConnective.HomClass.map_and,argumentGraphs_eval,
    eval_graph_rel,Semiterm.val,Matrix.appeendr_addCast,Matrix.appeendr_addNat,termGraph_eval]
  change (∃ values : Fin k → A,
    (∀ i, values i = (args i).valb env) ∧ Tarski.Structure.rel (L := FilterLanguage) symbol values) ↔ _
  constructor
  · rintro ⟨values,equal,holds⟩
    rw [show values = (fun i => (args i).valb env) from funext equal] at holds
    exact holds
  · intro holds
    exact ⟨_,fun _ => rfl,holds⟩

theorem graphFormula_eval {n : Nat} (p : Semisentence FilterLanguage n) (env : Fin n → A) :
    (graphFormula p).Evalb env ↔ p.Evalb env := by
  induction p with
  | verum | falsum => rfl
  | rel symbol args => exact graphAtom_eval symbol args env
  | nrel symbol args =>
    rw [graphFormula,LogicalConnective.HomClass.map_neg]
    exact not_congr (graphAtom_eval symbol args env)
  | and p q left right => exact and_congr (left env) (right env)
  | or p q left right => exact or_congr (left env) (right env)
  | all p ih => exact forall_congr' fun x => ih (x :> env)
  | exs p ih => exact exists_congr fun x => ih (x :> env)

end Semantics
end PalomarI3380.Calibration
