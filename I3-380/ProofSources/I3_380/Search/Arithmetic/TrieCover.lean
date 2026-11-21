module
public import I3_380.Search.Arithmetic.TriePrograms
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceCantor (pairValue)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The meaning of one row, independently of the pending and selector
registers used by the trie. Intermediate stores are typed stores. -/
inductive CodedPatternTrace : List Pattern → Store M → Store M → Prop
  | nil (s) : CodedPatternTrace [] s s
  | cons {first : Pattern} {rest : List Pattern} {s t f : Store M}
      (run : ∀ p r, first.compile.Runs .normal (controls s p r).code (controls t p r).code)
      (ready : ClearScratch t) (tail : CodedPatternTrace rest t f) : CodedPatternTrace (first :: rest) s f

theorem CodedPatternTrace.lines {ps : List Pattern} {s t : Store M}
    (trace : CodedPatternTrace ps s t) (p r : M) :
    CodedLines (ps.map Pattern.compile) (controls s p r).code (controls t p r).code := by
  induction trace with
  | nil => exact .nil _
  | cons exec _ _ ih => exact .cons (exec p r) ih

theorem CodedPatternTrace.trans {ps qs : List Pattern} {s t f : Store M}
    (first : CodedPatternTrace ps s t) (second : CodedPatternTrace qs t f) :
    CodedPatternTrace (ps ++ qs) s f := by
  induction first with
  | nil => exact second
  | cons head ready _ ih => exact .cons head ready (ih second)

noncomputable def modelFields : List Nat → M → M
  | [], suffix => suffix
  | i::is, suffix => pairValue (i : M) (modelFields is suffix)

theorem modelFields_append (leading trailing : List Nat) (tail : M) :
    modelFields (leading ++ trailing) tail = modelFields leading (modelFields trailing tail) := by
  induction leading with
  | nil => rfl
  | cons i is ih => exact congrArg (pairValue (i : M)) ih

theorem coded_choose_exact (branch : Option Pattern → List Program) (keys : List (Option Pattern))
    (key : Option Pattern) (belongs : key ∈ keys) :
    ∃ leading : List Nat, ∀ s t : Store M, ∀ suffix : M, ClearScratch s →
      CodedLines (branch key) (controls s suffix 0).code t.code →
      CodedLines (chooseBranches branch keys) (controls s (modelFields leading suffix) 0).code t.code := by
  rcases keys with _ | ⟨a,_ | ⟨b,ks⟩⟩
  · simp at belongs
  · have : key=a := List.mem_singleton.mp belongs
    subst key
    exact ⟨[],fun _ _ _ _ exec => exec⟩
  obtain ⟨i,within,label⟩ := List.mem_iff_getElem.mp belongs
  refine ⟨[i],fun s t suffix clear exec => ?_⟩
  let start := controls s (pairValue (i : M) suffix) 0
  let next := controls s suffix (i : M)
  have ready := clear.controls (pairValue (i : M) suffix) 0
  have selector := coded_read_pair (dst := sel) (by decide) (by decide) start
    ready.tokZero ready.auxZero (i : M) suffix (controls_pl ..)
  have step : (read sel).Runs .normal start.code next.code := by
    change (read sel).Runs .normal start.code (controls start suffix (start sel+(i : M))).code at selector
    simpa only [start,controls_sel,zero_add,controls_override] using selector
  have selection : modelSelect (((a::b::ks).map fun k => block (branch k))) (next sel) =
      some (block (branch key),0) := by
    have picked := modelSelect_exact (M := M) (a::b::ks) i within
    rw [label] at picked
    rw [modelSelect_map,show next sel = (i : M) from controls_sel ..,picked]
    rfl
  have runBranch : (block (branch key)).Runs .normal (next.set sel 0).code t.code := by
    rw [show next.set sel 0 = controls s suffix 0 from Store.set_set ..]
    exact exec.block
  exact .cons step (.cons (coded_dispatch _ next selection runBranch) (.nil _))

theorem coded_trie_cover (fuel : Nat) (rows : List (List Pattern))
    (adequate : ∀ row ∈ rows, row.length ≤ fuel) (row : List Pattern) (member : row ∈ rows) :
    ∃ fields : List Nat, ∀ s t : Store M, ∀ tail, ClearScratch s →
      CodedPatternTrace row s t → ClearScratch t →
      CodedLines (trie fuel rows) (controls s (modelFields fields tail) 0).code (controls t tail 0).code := by
  induction fuel generalizing rows row with
  | zero =>
    have empty : row = [] := by simpa using adequate row member
    subst row
    exact ⟨[],fun s t tail _ trace _ => by cases trace; exact .nil _⟩
  | succ fuel ih =>
    rcases rows with _ | ⟨first,_ | ⟨second,more⟩⟩
    · simp at member
    · obtain rfl := List.mem_singleton.mp member
      exact ⟨[],fun _ _ tail _ trace _ => trace.lines tail 0⟩
    let rows := first :: second :: more
    let branch := trieBranch (trie fuel) rows
    have select := coded_choose_exact (M := M) branch (branchKeys rows) row.head? (key_of_row member)
    obtain ⟨leading,load⟩ := select
    have branchExec :
        ∃ fields : List Nat, ∀ s t : Store M, ∀ tail, ClearScratch s →
          CodedPatternTrace row s t → ClearScratch t →
          CodedLines (branch row.head?) (controls s (modelFields fields tail) 0).code (controls t tail 0).code := by
      cases row with
      | nil => exact ⟨[],fun s t tail _ trace _ => by cases trace; exact .nil _⟩
      | cons first rest =>
        have enough : ∀ row ∈ branchTail (some first) rows, row.length ≤ fuel := by
          intro r belongs
          exact Nat.le_of_succ_le_succ (adequate _ (branchTail_mem.mp belongs))
        obtain ⟨fields,restExec⟩ := ih _ enough rest (branchTail_mem.mpr member)
        refine ⟨fields,fun s t tail ready trace readyEnd => ?_⟩
        cases trace with
        | cons head readyNext runs =>
          exact .cons (head _ _) (restExec _ _ tail readyNext runs readyEnd)
    obtain ⟨fields,execution⟩ := branchExec
    refine ⟨leading ++ fields,fun s t tail ready trace last => ?_⟩
    rw [modelFields_append]
    exact load s (controls t tail 0) (modelFields fields tail) ready (execution s t tail ready trace last)

theorem coded_rows_cover {equation : Equation} (member : equation ∈ rows) :
    ∃ fields : List Nat, ∀ s t : Store M, ∀ tail, ClearScratch s →
      CodedPatternTrace (rowPattern equation) s t → ClearScratch t →
      CodedLines compiledRows (controls s (modelFields fields tail) 0).code (controls t tail 0).code :=
  coded_trie_cover _ _ (foldMaximum _ 0).2 _ (List.mem_map.mpr ⟨equation,member,rfl⟩)

end PalomarI3380.Compiler.Source
