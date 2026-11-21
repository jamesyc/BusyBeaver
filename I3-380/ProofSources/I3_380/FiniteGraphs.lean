module
public import I3_380.ModelSyntax
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

theorem mem_numeral (n : Nat) (x : V) :
    N.mem x (N.numeral n) ↔ ∃ i, i < n ∧ x = N.numeral i := by
  induction n with
  | zero =>
    exact ⟨fun h => (N.empty_mem x h).elim,fun ⟨i,hi,_⟩ => (Nat.not_lt_zero _ hi).elim⟩
  | succ n ih =>
    change N.mem x (N.succ (N.numeral n)) ↔ _
    rw [N.mem_succ,ih]
    constructor
    · rintro (⟨i,hi,eq⟩ | eq)
      · exact ⟨i,by omega,eq⟩
      · exact ⟨n,Nat.lt_succ_self _,eq⟩
    · rintro ⟨i,hi,eq⟩
      by_cases same : i = n
      · exact Or.inr (eq.trans (congrArg N.numeral same))
      · exact Or.inl ⟨i,by omega,eq⟩

noncomputable def numberedGraph : Nat → List V → V
  | _, [] => N.empty
  | i, a::rest => N.union₂ (N.singleton (N.orderedPair (N.numeral i) a)) (numberedGraph (i+1) rest)

theorem mem_numberedGraph (values : List V) (offset : Nat) (p : V) :
    N.mem p (N.numberedGraph offset values) ↔ ∃ i : Fin values.length,
      p = N.orderedPair (N.numeral (offset + i.val)) values[i.val] := by
  induction values generalizing offset with
  | nil =>
    constructor
    · exact fun h => (N.empty_mem _ h).elim
    · rintro ⟨i,_⟩
      exact (Nat.not_lt_zero _ i.isLt).elim
  | cons v rest ih =>
    rw [numberedGraph,N.mem_union₂,N.mem_singleton,ih]
    constructor
    · rintro (front | ⟨i,tail⟩)
      · refine ⟨⟨0,Nat.zero_lt_succ _⟩,?_⟩
        simpa using front
      · refine ⟨⟨i.val+1,by have := i.isLt; simp only [List.length_cons]; omega⟩,?_⟩
        simpa only [List.getElem_cons_succ,show offset + (i.val+1) = offset + 1 + i.val by omega] using tail
    · rintro ⟨⟨i, hi⟩,value⟩
      cases i with
      | zero => exact Or.inl (by simpa using value)
      | succ i =>
        have idx : i < rest.length := by simp only [List.length_cons] at hi; omega
        exact Or.inr ⟨⟨i,idx⟩,by
          simpa only [List.getElem_cons_succ,show offset + (i+1) = offset + 1 + i by omega] using value⟩

noncomputable def listGraph (values : List V) : V := N.numberedGraph 0 values

theorem listGraph_value (values : List V) (i y : V) :
    Internal.At N.mem (N.listGraph values) i y ↔ ∃ j : Fin values.length,
      i = N.numeral j.val ∧ y = values[j.val] := by
  rw [N.at_pair]
  change N.mem (N.orderedPair i y) (N.numberedGraph 0 values) ↔ _
  rw [N.mem_numberedGraph]
  apply exists_congr
  intro j
  simp only [Nat.zero_add]
  exact ⟨N.orderedPair_inj,fun ⟨a,b⟩ => by rw [a,b]⟩

theorem listGraph_function (values : List V) :
    Internal.FunctionOn N.mem (N.listGraph values) (N.numeral values.length) := by
  refine ⟨?_,?_⟩
  · intro i hi
    obtain ⟨j,ordinal,same⟩ := (N.mem_numeral _ _).mp hi
    let index : Fin values.length := ⟨j,ordinal⟩
    refine ⟨values[j],(N.listGraph_value _ _ _).mpr ⟨index,same,rfl⟩,fun z hz => ?_⟩
    obtain ⟨k,one,valid⟩ := (N.listGraph_value _ _ _).mp hz
    have which := N.numeral_injective (one.symm.trans same)
    exact valid.trans (by simp [which])
  · intro p hp
    obtain ⟨j,code⟩ := (N.mem_numberedGraph values 0 p).mp hp
    refine ⟨N.numeral j.val,values[j.val],(N.mem_numeral _ _).mpr ⟨j.val,j.isLt,rfl⟩,?_⟩
    rw [code,Nat.zero_add]
    exact N.orderedPair_intro _ _

theorem listGraph_into (values : List V) (stage : V) (inside : ∀ y ∈ values, N.mem y stage) :
    Internal.FunctionInto N.mem (N.listGraph values) (N.numeral values.length) stage := by
  refine ⟨N.listGraph_function _,fun i _ y value => ?_⟩
  obtain ⟨j,_,same⟩ := (N.listGraph_value _ _ _).mp value
  exact same.symm ▸ inside _ (List.getElem_mem _)

end PalomarI3380.SquareRepresentation.SetContext
