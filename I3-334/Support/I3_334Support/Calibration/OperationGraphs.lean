module
public import I3_334Support.Calibration.RelationalFormulas
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder


def operationAtom {n k : Nat} (symbol : FunctionSymbol k)
    (values : Fin (k+1) → ClosedSemiterm GraphLanguage n) : Semisentence GraphLanguage n :=
  .rel (.operation symbol) values

def operationTotal {k : Nat} (symbol : FunctionSymbol k) : FFL.FirstOrder.Sentence GraphLanguage :=
  ∀¹* (∃¹ operationAtom symbol Semiterm.bvar)

def operationUnique {k : Nat} (symbol : FunctionSymbol k) : FFL.FirstOrder.Sentence GraphLanguage :=
  ∀¹* (operationAtom symbol (.bvar 0 :> fun i => .bvar i.succ.succ) 🡒
    operationAtom symbol (.bvar 1 :> fun i => .bvar i.succ.succ) 🡒
    .rel (.relation .equal) ![.bvar 0,.bvar 1])

section Semantics

variable {A : Type} [Tarski.Structure GraphLanguage A]

theorem graphSymbol_eval {k n : Nat} (symbol : GraphSymbol k)
    (terms : Fin k → ClosedSemiterm GraphLanguage n) (env : Fin n → A) :
    (Semiformula.rel (L := GraphLanguage) symbol terms).Evalb env ↔
    Tarski.Structure.rel (L := GraphLanguage) symbol (fun i => (terms i).valb env) := Iff.rfl

def graphOutput {k : Nat} (symbol : FunctionSymbol k) (args : Fin k → A) (value : A) : Prop :=
  Tarski.Structure.rel (L := GraphLanguage) (GraphSymbol.operation symbol) (value :> args)

theorem operationTotal_eval [Nonempty A] {k : Nat} (symbol : FunctionSymbol k) :
    A↓[GraphLanguage] ⊧ operationTotal symbol ↔ ∀ args : Fin k → A, ∃ out : A, graphOutput symbol args out := by
  simp [operationTotal,models_iff,operationAtom,graphOutput,graphSymbol_eval,Semiterm.valb,Semiterm.val]

theorem operationUnique_eval [Nonempty A] [Tarski.Structure.Eq GraphLanguage A]
    {k : Nat} (symbol : FunctionSymbol k) :
    A↓[GraphLanguage] ⊧ operationUnique symbol ↔
      ∀ (a b : A) (args : Fin k → A), graphOutput symbol args a → graphOutput symbol args b → a = b := by
  simp only [operationUnique,models_iff,Semiformula.eval_allClosure,Matrix.vecForall_iff]
  apply forall_congr'
  intro a
  apply forall_congr'
  intro b
  apply forall_congr'
  intro args
  simp only [LogicalConnective.HomClass.map_imply,operationAtom,graphSymbol_eval,Semiterm.valb]
  have aArgs : (fun i : Fin (k+1) => Semiterm.val (a :> b :> args) Empty.elim
      ((.bvar 0 :> fun j => .bvar j.succ.succ) i : ClosedSemiterm GraphLanguage (k+2))) = (a :> args) := by
    funext i
    cases i using Fin.cases <;> rfl
  have bArgs : (fun i : Fin (k+1) => Semiterm.val (a :> b :> args) Empty.elim
      ((.bvar 1 :> fun j => .bvar j.succ.succ) i : ClosedSemiterm GraphLanguage (k+2))) = (b :> args) := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [aArgs,bArgs]
  have same : Tarski.Structure.rel (L := GraphLanguage) (GraphSymbol.relation .equal)
      (fun i : Fin 2 => Semiterm.val (a :> b :> args) Empty.elim
        (![.bvar 0,.bvar 1] i : ClosedSemiterm GraphLanguage (k+2))) ↔ a=b := by
    have values : (fun i : Fin 2 => Semiterm.val (a :> b :> args) Empty.elim
        (![.bvar 0,.bvar 1] i : ClosedSemiterm GraphLanguage (k+2))) = ![a,b] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      have zero : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
    rw [values]
    exact Tarski.Structure.Eq.eq (L := GraphLanguage) a b
  exact imp_congr_right (fun _ => imp_congr_right fun _ => same)

structure HasOperationGraphs : Prop where
  total : ∀ {k : Nat} (symbol : FunctionSymbol k) (args : Fin k → A), ∃ out, graphOutput symbol args out
  unique : ∀ {k : Nat} (symbol : FunctionSymbol k) (args : Fin k → A) (a b : A),
    graphOutput symbol args a → graphOutput symbol args b → a=b

@[instance_reducible] noncomputable def restoreStructure (graphs : HasOperationGraphs (A := A)) :
    Tarski.Structure FilterLanguage A where
  func {k} f args := Classical.choose (graphs.total (show FunctionSymbol k from f) args)
  rel {k} r vals := Tarski.Structure.rel (L := GraphLanguage)
    (GraphSymbol.relation (show RelationSymbol k from r)) vals

theorem restoreStructure_relational (graphs : HasOperationGraphs (A := A)) :
    @graphStructure A (restoreStructure graphs) = (inferInstance : Tarski.Structure GraphLanguage A) := by
  ext k symbol vals
  · exact symbol.elim
  · cases symbol with
    | relation r => rfl
    | @operation n f =>
      let args : Fin n → A := fun i => vals i.succ
      have witness := Classical.choose_spec (graphs.total f args)
      have represent : (vals 0 :> args) = vals := Matrix.eq_vecCons vals
      change vals 0 = Classical.choose (graphs.total f args) ↔
        Tarski.Structure.rel (L := GraphLanguage) (GraphSymbol.operation f) vals
      have output : Tarski.Structure.rel (L := GraphLanguage) (GraphSymbol.operation f) vals ↔
          graphOutput f args (vals 0) := by rw [graphOutput,represent]
      rw [output]
      exact ⟨fun eq => by rw [eq]; exact witness,fun h => graphs.unique f args _ _ h witness⟩

theorem restoreStructure_eq [Tarski.Structure.Eq GraphLanguage A]
    (graphs : HasOperationGraphs (A := A)) :
    letI := restoreStructure graphs
    Tarski.Structure.Eq FilterLanguage A := by
  letI := restoreStructure graphs
  exact ⟨fun a b => Tarski.Structure.Eq.eq (L := GraphLanguage) a b⟩

end Semantics
end PalomarI3380.Calibration
