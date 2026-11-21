module
public import I3_380.Search.Arithmetic.CounterPrograms
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The branch list is fixed by the source. A model-valued selector
may exceed its length, in which case the final branch is used. -/
noncomputable def modelSelect {α : Type} : List α → M → Option (α × M)
  | [], _ => none
  | [p], n => some (p,n)
  | p::q::ps, n => if n=0 then some (p,0) else modelSelect (q::ps) (n-1)

theorem modelSelect_exists {α : Type} {ps : List α} (nonempty : ps ≠ []) (n : M) :
    ∃ p r, p ∈ ps ∧ modelSelect ps n = some (p,r) := by
  induction ps generalizing n with
  | nil => exact (nonempty rfl).elim
  | cons p rest ih =>
    cases rest with
    | nil => exact ⟨p,n,by simp,rfl⟩
    | cons q qs =>
      by_cases zero : n=0
      · exact ⟨p,0,by simp,by simp [modelSelect,zero]⟩
      · obtain ⟨selected,leftover,belongs,eq⟩ := ih (by simp) (n-1)
        exact ⟨selected,leftover,List.mem_cons_of_mem p belongs,by simp [modelSelect,zero,eq]⟩

theorem modelSelect_map {α β : Type} (f : α → β) (ps : List α) (n : M) :
    modelSelect (ps.map f) n = (modelSelect ps n).map (fun (p,r) => (f p,r)) := by
  induction ps generalizing n with
  | nil => rfl
  | cons p ps ih =>
    cases ps with
    | nil => rfl
    | cons q qs =>
      by_cases zero : n=0
      · simp [List.map_cons,modelSelect,zero]
      · simpa only [List.map_cons,modelSelect,zero,↓reduceIte] using ih (n-1)

theorem modelSelect_exact {α : Type} (ps : List α) (n : Nat) (bound : n < ps.length) :
    modelSelect ps (n : M) = some (ps[n],0) := by
  induction ps generalizing n with
  | nil => simp at bound
  | cons p ps ih =>
    cases ps with
    | nil =>
      have zero : n=0 := Nat.lt_one_iff.mp bound
      subst n
      simp [modelSelect]
    | cons q qs =>
      cases n with
      | zero => simp [modelSelect]
      | succ n =>
        have nz : (n : M)+1 ≠ 0 := (lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)).ne'
        simp only [modelSelect,Nat.cast_succ,nz,↓reduceIte,Arithmetic.add_sub_self]
        exact ih n (by simpa using bound)

theorem coded_dispatch (ps : List Program) (s : Store M) {branch : Program} {r : M} {final : M}
    (selection : modelSelect ps (s sel) = some (branch,r))
    (run : branch.Runs .normal (s.set sel r).code final) :
    (dispatch ps).Runs .normal s.code final := by
  induction ps generalizing s branch r final with
  | nil => simp [modelSelect] at selection
  | cons first rest ih =>
    cases rest with
    | nil =>
      simp only [modelSelect,Option.some.injEq,Prod.mk.injEq] at selection
      obtain ⟨rfl,rfl⟩ := selection
      simpa only [dispatch,Store.set_same] using run
    | cons next ps =>
      by_cases zero : s sel=0
      · simp only [modelSelect,zero,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at selection
        obtain ⟨rfl,rfl⟩ := selection
        have unchanged : s.set sel 0=s := by rw [← zero,Store.set_same]
        rw [unchanged] at run
        exact Program.Runs.rightExit (Program.Runs.leftExit (coded_decrement_zero zero) rfl) run rfl
      · let nextState := s.set sel (s sel-1)
        have selected : modelSelect (next::ps) (nextState sel) = some (branch,r) := by
          simpa only [modelSelect,zero,↓reduceIte,nextState,Store.get_set] using selection
        have child : branch.Runs .normal (nextState.set sel r).code final := by
          simpa only [nextState,Store.set_set] using run
        have tail := ih nextState selected child
        have canBreak : (break_ 1).Runs (.escape 0) final final := ⟨rfl,rfl⟩
        exact Program.Runs.leftExit
          (Program.Runs.rightExit (coded_decrement_positive zero)
            (Program.Runs.rightExit tail canBreak rfl) rfl) rfl

end PalomarI3380.Compiler.Source
