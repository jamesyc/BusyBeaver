module
public import I3_380.Calibration.FilterCoding
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- Replace each operation by its graph, with the output at position zero.
Formulas used by the internal interpretation then have only variable terms. -/
inductive GraphSymbol : Nat → Type where
  | relation {n : Nat} : RelationSymbol n → GraphSymbol n
  | operation {n : Nat} : FunctionSymbol n → GraphSymbol (n+1)
  deriving DecidableEq

def GraphLanguage : Language := ⟨fun _ => Empty,GraphSymbol⟩

instance : GraphLanguage.Eq := ⟨.relation .equal⟩

def graphSymbols : (n : Nat) → List (GraphSymbol n)
  | 0 => []
  | n+1 => (relations (n+1)).map .relation ++ (functions n).map .operation

theorem graphSymbols_complete {n : Nat} (symbol : GraphSymbol n) :
    symbol ∈ graphSymbols n := by
  cases symbol with
  | relation r =>
    cases r <;> simp [graphSymbols,relations]
  | operation f =>
    exact List.mem_append_right _ (List.mem_map.mpr ⟨f,functions_complete f,rfl⟩)

theorem graphSymbols_distinct (n : Nat) : (graphSymbols n).Nodup := by
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      cases n with
      | zero => decide
      | succ n =>
        cases n with
        | zero => decide
        | succ n => cases n <;> simp [graphSymbols,relations,functions]

instance : GraphLanguage.Encodable where
  func _ := inferInstanceAs (Encodable Empty)
  rel n := listCoding (X := GraphSymbol n) (graphSymbols n) graphSymbols_complete

instance : GraphLanguage.DecidableEq where
  func _ := inferInstanceAs (DecidableEq Empty)
  rel n := inferInstanceAs (DecidableEq (GraphSymbol n))

instance : GraphLanguage.Finite where
  func := Fintype.ofList [] (by rintro ⟨_,f⟩; exact f.elim)
  rel := Fintype.ofList ((List.range 5).flatMap fun n => (graphSymbols n).map (Sigma.mk n)) (by
    rintro ⟨n,r⟩
    have bounded : n < 5 := by cases r with
      | relation r => cases r <;> decide
      | operation f => cases f <;> decide
    exact List.mem_flatMap.mpr ⟨n,List.mem_range.mpr bounded,List.mem_map.mpr ⟨r,graphSymbols_complete r,rfl⟩⟩)

instance : GraphLanguage.LORDefinable where
  func := .mkSigma “arity tag. ⊥”
  rel := .mkSigma “arity tag. (arity = 1 ∧ tag < 8) ∨ (arity = 2 ∧ tag < 5) ∨
    (arity = 3 ∧ tag < 2) ∨ (arity = 4 ∧ tag = 0)”
  func_iff := by
    intro n tag
    simp only [Set.mem_range]
    constructor
    · rintro ⟨f,_⟩
      exact f.elim
    · simp
  rel_iff := by
    intro n tag
    simp only [Set.mem_range]
    change (∃ r : GraphSymbol n, (listCoding (X := GraphSymbol n) (graphSymbols n) graphSymbols_complete).encode r = tag) ↔ _
    rw [listCoding_range _ (graphSymbols_distinct n)]
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with
      rfl | rfl | rfl | rfl | rfl | bigger
    · simp [graphSymbols]
    · simp [graphSymbols,relations,functions]
    · simp [graphSymbols,relations,functions]
    · simp [graphSymbols,relations,functions]; omega
    · simp [graphSymbols,relations,functions]
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le bigger
      rw [Nat.add_comm 5 k]
      simp [graphSymbols,relations,functions]

@[instance_reducible] def graphStructure {A : Type} [Tarski.Structure FilterLanguage A] :
    Tarski.Structure GraphLanguage A where
  func {_} symbol _ := symbol.elim
  rel {k} symbol assignment := match (show GraphSymbol k from symbol) with
    | .relation r => Tarski.Structure.rel (L := FilterLanguage) r assignment
    | .operation f => assignment 0 = Tarski.Structure.func (L := FilterLanguage) f (fun i => assignment i.succ)

theorem graphStructure_eq {A : Type} [Tarski.Structure FilterLanguage A] [Tarski.Structure.Eq FilterLanguage A] :
    letI := graphStructure (A := A)
    Tarski.Structure.Eq GraphLanguage A := by
  letI := graphStructure (A := A)
  exact ⟨fun a b => Tarski.Structure.Eq.eq (L := FilterLanguage) a b⟩

@[simp] theorem graphLanguage_no_function {M : Type*} [ORingStructure M]
    {arity code : M} : ¬GraphLanguage.IsFunc arity code := by
  change ¬(⊥ : Semisentence ℒₒᵣ 2).Evalb ![arity,code]
  simp

end PalomarI3380.Calibration
