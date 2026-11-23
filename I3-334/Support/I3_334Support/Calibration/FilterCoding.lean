module
public import I3_334Support.Calibration.FilterTheory
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Theory
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def functions : (k : Nat) → List (FunctionSymbol k)
  | 0 => [.constant .J,.constant .D,.constant .T,.constant .S,.constant .U,.constant .E,.constant .I]
  | 1 => [.complement,.choose,.localRelation,.converse]
  | 2 => [.nand,.product]
  | 3 => [.node]
  | _+4 => []

def relations : (k : Nat) → List (RelationSymbol k)
  | 1 => [.chosen]
  | 2 => [.equal]
  | _ => []

theorem functions_complete {k : Nat} (symbol : FunctionSymbol k) : symbol ∈ functions k := by
  cases symbol with
  | constant c => cases c <;> simp [functions]
  | _ => simp [functions]

theorem relations_complete {k : Nat} (symbol : RelationSymbol k) : symbol ∈ relations k := by
  cases symbol <;> simp [relations]

theorem functions_distinct (k : Nat) : (functions k).Nodup := by
  cases k with
  | zero => decide
  | succ k =>
    cases k with
    | zero => decide
    | succ k =>
      cases k with
      | zero => decide
      | succ k => cases k <;> simp [functions]

theorem relations_distinct (k : Nat) : (relations k).Nodup := by
  cases k with
  | zero => decide
  | succ k =>
    cases k with
    | zero => decide
    | succ k => cases k <;> simp [relations]

def listCoding {X : Type} [DecidableEq X] (symbols : List X) (covers : ∀ x, x ∈ symbols) :
    Encodable X where
  encode x := symbols.idxOf x
  decode n := symbols[n]?
  encodek x := List.getElem?_idxOf (covers x)

instance : FilterLanguage.Encodable where
  func k := listCoding (X := FunctionSymbol k) (functions k) functions_complete
  rel k := listCoding (X := RelationSymbol k) (relations k) relations_complete

instance : FilterLanguage.DecidableEq where
  func k := inferInstanceAs (DecidableEq (FunctionSymbol k))
  rel k := inferInstanceAs (DecidableEq (RelationSymbol k))

instance : FilterLanguage.Finite where
  func := Fintype.ofList ((List.range 4).flatMap fun k => (functions k).map (Sigma.mk k)) (by
    rintro ⟨k,f⟩
    have hk : k < 4 := by cases f <;> decide
    exact List.mem_flatMap.mpr ⟨k,List.mem_range.mpr hk,List.mem_map.mpr ⟨f,functions_complete f,rfl⟩⟩)
  rel := Fintype.ofList ((List.range 3).flatMap fun k => (relations k).map (Sigma.mk k)) (by
    rintro ⟨k,r⟩
    have hk : k < 3 := by cases r <;> decide
    exact List.mem_flatMap.mpr ⟨k,List.mem_range.mpr hk,List.mem_map.mpr ⟨r,relations_complete r,rfl⟩⟩)

theorem listCoding_range {X : Type} [DecidableEq X] (symbols : List X) (distinct : symbols.Nodup)
    (covers : ∀ x, x ∈ symbols) (n : Nat) :
    (∃ x, (listCoding symbols covers).encode x = n) ↔ n < symbols.length := by
  constructor
  · rintro ⟨x,rfl⟩
    exact List.idxOf_lt_length_of_mem (covers x)
  · intro hn
    refine ⟨symbols[n],?_⟩
    exact distinct.idxOf_getElem n hn

instance : FilterLanguage.LORDefinable where
  func := .mkSigma “k c. (k = 0 ∧ c < 7) ∨ (k = 1 ∧ c < 4) ∨ (k = 2 ∧ c < 2) ∨ (k = 3 ∧ c < 1)”
  rel := .mkSigma “k c. (k = 1 ∧ c < 1) ∨ (k = 2 ∧ c < 1)”
  func_iff := by
    intro k c
    change (∃ x, (listCoding (functions k) functions_complete).encode x = c) ↔ _
    rw [listCoding_range _ (functions_distinct k)]
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
    rcases hk with rfl | rfl | rfl | rfl | other
    · simp [functions] <;> omega
    · simp [functions] <;> omega
    · simp [functions] <;> omega
    · simp [functions] <;> omega
    · have none : (functions k).length = 0 := by
        obtain ⟨i,eq⟩ := Nat.exists_eq_add_of_le other
        rw [eq, Nat.add_comm 4 i]
        rfl
      rw [none]
      simp
      omega
  rel_iff := by
    intro k c
    change (∃ x, (listCoding (relations k) relations_complete).encode x = c) ↔ _
    rw [listCoding_range _ (relations_distinct k)]
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
    rcases hk with rfl | rfl | rfl | other
    · simp [relations] <;> omega
    · simp [relations] <;> omega
    · simp [relations] <;> omega
    · have none : (relations k).length = 0 := by
        obtain ⟨i,eq⟩ := Nat.exists_eq_add_of_le other
        rw [eq,Nat.add_comm 3 i]
        rfl
      rw [none]
      simp
      omega

noncomputable instance : filterTheory.Δ₁ :=
  (Theory.Δ₁.ofFinite _ Theory.EqAxiom.finite).add
    (Theory.Δ₁.ofList (filterSentence :: Manifest.preceding.map equationSentence))


end PalomarI3380.Calibration
