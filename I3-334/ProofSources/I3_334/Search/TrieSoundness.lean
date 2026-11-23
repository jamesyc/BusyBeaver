module
public import I3_334.Search.TrieSelection
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (LineRuns)
open Templates (Instruction)

structure TrieResult (fuel : Nat) (table : List (List Instruction)) (s : Store) where
  row : List Instruction
  finish : Store
  listed : row ∈ table
  executed : LineRuns (trie fuel table) s finish
  scratch : Scratch finish
  observed : FrontBounds (instructionsEffect row s) finish
  pending : finish pl ≤ s pl

theorem branch_head {table : List (List Instruction)} {key : Option Instruction}
    (selected : key ∈ branchKeys table) : ∃ row ∈ table, row.head? = key := by
  unfold branchKeys at selected
  have listed : key ∈ table.map List.head? := List.mem_eraseDups.mp selected
  exact List.mem_map.mp listed

theorem branch_tail {table : List (List Instruction)} {i : Instruction} {row : List Instruction}
    (listed : row ∈ branchRows (some i) table) : i :: row ∈ table := by
  obtain ⟨xs,choice,tail⟩ := List.mem_map.mp listed
  obtain ⟨isMember,head⟩ := List.mem_filter.mp choice
  have token : xs.head? = some i := beq_iff_eq.mp head
  cases xs with
  | nil => simp at token
  | cons first rest =>
    have same : first = i := Option.some.inj token
    subst first
    exact tail ▸ isMember

/-- Every execution constructed by the compiled trie comes from one of
its declared templates. An out-of-range selector can only saturate at
a declared branch, and the selected scratch counters cannot change the
proof fronts. -/
theorem trie_runs (fuel : Nat) (table : List (List Instruction)) (s : Store)
    (ready : Scratch s) (nonempty : table ≠ [])
    (covers : ∀ row ∈ table, row.length ≤ fuel) :
    Nonempty (TrieResult fuel table s) := by
  induction fuel generalizing table s with
  | zero =>
    cases table with
    | nil => exact (nonempty rfl).elim
    | cons w words =>
      have len := covers w List.mem_cons_self
      have empty : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero len)
      subst w
      exact ⟨⟨[],s,List.mem_cons_self,.nil,ready,FrontBounds.refl s,Nat.le_refl _⟩⟩
  | succ fuel ih =>
    cases table with
    | nil => exact (nonempty rfl).elim
    | cons first remaining =>
      cases remaining with
      | nil =>
        obtain ⟨run,clean⟩ := instructions_run first s ready
        refine ⟨⟨first,instructionsEffect first s,List.mem_cons_self,run,clean,
          FrontBounds.refl _,?_⟩⟩
        simpa only [instructions_pending] using Nat.le_refl (s pl)
      | cons second rest =>
        let table := first :: second :: rest
        let keys := branchKeys table
        let compile := fun key : Option Instruction => match key with
          | none => []
          | some i => instruction i :: trie fuel (branchRows key table)
        have keysExist : keys ≠ [] := by
          have given : first.head? ∈ keys := by
            unfold keys branchKeys
            exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨first,List.mem_cons_self,rfl⟩)
          exact fun empty => by simp [empty] at given
        obtain ⟨choice⟩ := choose_runs keys compile s ready keysExist
        cases key : choice.key with
        | none =>
          have listed : none ∈ branchKeys table := key ▸ choice.member
          obtain ⟨row,mem,noHead⟩ := branch_head listed
          have empty : row = [] := List.head?_eq_none_iff.mp noHead
          subst row
          have branch : LineRuns (compile choice.key) choice.start choice.start := by
            rw [key]
            exact .nil
          exact ⟨⟨[],choice.start,mem,choice.execute branch,choice.scratch,choice.observed,choice.pending⟩⟩
        | some i =>
          let tail := branchRows (some i) table
          let middle := instructionEffect i choice.start
          have listed : some i ∈ branchKeys table := key ▸ choice.member
          have notEmpty : tail ≠ [] := by
            obtain ⟨row,mem,head⟩ := branch_head listed
            have fits : row.tail ∈ tail := by
              apply List.mem_map.mpr
              exact ⟨row,List.mem_filter.mpr ⟨mem,beq_iff_eq.mpr head⟩,rfl⟩
            exact fun impossible => by simp [impossible] at fits
          have length (row : List Instruction) (listed : row ∈ tail) : row.length ≤ fuel := by
            have known := covers (i::row) (branch_tail listed)
            simp only [List.length_cons] at known
            omega
          obtain ⟨suffix⟩ := ih tail middle (instruction_clean i choice.start choice.scratch) notEmpty length
          have branch : LineRuns (compile choice.key) choice.start suffix.finish := by
            rw [key]
            exact .cons (run_instruction i choice.start choice.scratch) suffix.executed
          have view := (instructions_observe suffix.row (instruction_observe i choice.observed)).trans suffix.observed
          have pending := suffix.pending
          change suffix.finish pl ≤ instructionEffect i choice.start pl at pending
          rw [instruction_pending] at pending
          exact ⟨⟨i :: suffix.row,suffix.finish,branch_tail suffix.listed,choice.execute branch,
            suffix.scratch,view,Nat.le_trans pending choice.pending⟩⟩

end PalomarI3334.SearchProgram
