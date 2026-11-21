module
public import I3_380.Search.Compiler.Dispatch
@[expose] public section

namespace PalomarI3380.Compiler.Source

def controls {V : Type} (s : Store V) (pending selector : V) : Store V :=
  (s.set pl pending).set sel selector

theorem controls_same {V : Type} (s : Store V) : controls s (s pl) (s sel) = s := by
  simp only [controls, Store.set_same]

theorem controls_override {V : Type} (s : Store V) (p q r t : V) :
    controls (controls s p q) r t = controls s r t := by
  unfold controls
  rw [Store.set_comm (s.set pl p) (by decide : sel ≠ pl), Store.set_set, Store.set_set]

theorem runPattern_controls (ps : List Pattern) (s : Store) (pending selector : Nat) :
    runPattern ps (controls s pending selector) = controls (runPattern ps s) pending selector := by
  unfold controls
  rw [runPattern_control _ _ sel _ (by decide) (by decide) (by decide) (by decide),
    runPattern_control _ _ pl _ (by decide) (by decide) (by decide) (by decide)]

private theorem exists_row_with_head {rows : List (List Pattern)} {key : Option Pattern}
    (member : key ∈ branchKeys rows) : ∃ row ∈ rows, row.head? = key := by
  have h : key ∈ rows.map List.head? := List.mem_eraseDups.mp member
  exact List.mem_map.mp h

theorem key_of_row {rows : List (List Pattern)} {row : List Pattern}
    (member : row ∈ rows) : row.head? ∈ branchKeys rows :=
  List.mem_eraseDups.mpr (List.mem_map.mpr ⟨row, member, rfl⟩)

theorem branch_empty {rows : List (List Pattern)} (h : none ∈ branchKeys rows) :
    [] ∈ rows := by
  obtain ⟨r, hr, empty⟩ := exists_row_with_head h
  cases r with
  | nil => exact hr
  | cons _ _ => simp at empty

theorem branchTail_mem {rows : List (List Pattern)} {head : Pattern} {tail : List Pattern} :
    tail ∈ branchTail (some head) rows ↔ head :: tail ∈ rows := by
  simp only [branchTail, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨row, ⟨hr, hh⟩, ht⟩
    cases row with
    | nil => simp at hh
    | cons p ps =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      cases hh
      change ps = tail at ht
      exact ht ▸ hr
  · exact fun h => ⟨_, ⟨h, rfl⟩, rfl⟩

theorem eligible_tail {rows : List (List Pattern)} {p : Pattern} (hp : some p ∈ branchKeys rows) :
    branchTail (some p) rows ≠ [] := by
  obtain ⟨row, mem, head⟩ := exists_row_with_head hp
  cases row with
  | nil => simp at head
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at head
    subst x
    have inside := (branchTail_mem (head := p)).mpr mem
    intro empty
    simp [empty] at inside

def TrieOutcome (program : List Program) (rows : List (List Pattern)) (s : Store) : Prop :=
  ∃ row ∈ rows, ∃ pending selector : Nat, pending ≤ s pl ∧
    LineRuns program s (controls (runPattern row s) pending selector)

private theorem runPattern_frame (row : List Pattern) (s : Store) (r : Register)
    (f : r ≠ fr) (l : r ≠ lv) (g : r ≠ gues) : runPattern row s r = s r := by
  induction row generalizing s with
  | nil => rfl
  | cons p ps ih => exact (ih (p.effect s)).trans (p.frame s r f l g)

private theorem leaf_run {rows : List (List Pattern)} (s : Store)
    (scratch : ClearScratch s) (row : List Pattern) (mem : row ∈ rows) :
    TrieOutcome (row.map Pattern.compile) rows s := by
  have unchangedP := runPattern_frame row s pl (by decide) (by decide) (by decide)
  have unchangedS := runPattern_frame row s sel (by decide) (by decide) (by decide)
  have effect : controls (runPattern row s) (s pl) (s sel) = runPattern row s := by
    rw [← unchangedP, ← unchangedS, controls_same]
  exact ⟨row, mem, s pl, s sel, Nat.le_refl _, effect.symm ▸ runPattern_compiled row s scratch⟩

set_option maxHeartbeats 6000000 in
/-- Every selector stream executes one of the literal rows. Out-of-range
selectors can change the following branch selection, but never create a
row outside the trie. -/
theorem run_trie (fuel : Nat) (rows : List (List Pattern)) (nonempty : rows ≠ [])
    (fuelBound : ∀ row ∈ rows, row.length ≤ fuel) (s : Store) (scratch : ClearScratch s) :
    TrieOutcome (trie fuel rows) rows s := by
  induction fuel generalizing rows s with
  | zero =>
    cases rows with
    | nil => contradiction
    | cons row rows =>
      have h := fuelBound row List.mem_cons_self
      have empty : row = [] := by simpa using h
      subst row
      exact leaf_run s scratch [] List.mem_cons_self
  | succ fuel ih =>
    cases rows with
    | nil => contradiction
    | cons first rest =>
      cases rest with
      | nil => exact leaf_run s scratch first List.mem_cons_self
      | cons second more =>
        let rows := first :: second :: more
        let keys := branchKeys rows
        let program := trieBranch (trie fuel) rows
        have branch (key : Option Pattern) (hKey : key ∈ keys) (start : Store)
            (ready : ClearScratch start) : TrieOutcome (program key) rows start := by
          cases key with
          | none => exact leaf_run start ready [] (branch_empty hKey)
          | some head =>
            have enough : ∀ suffix ∈ branchTail (some head) rows, suffix.length ≤ fuel := by
              intro suffix inside
              have h := fuelBound _ (branchTail_mem.mp inside)
              simp only [List.length_cons] at h
              omega
            obtain ⟨suffix, belongs, p, v, range, exec⟩ := ih (branchTail (some head) rows)
              (eligible_tail hKey) enough (head.effect start) (head.ready ready)
            have range' : p ≤ start pl := by
              rw [← head.frame start pl (by decide) (by decide) (by decide)]
              exact range
            exact ⟨head :: suffix, branchTail_mem.mp belongs, p, v, range',
              .cons (head.run start ready) exec⟩
        rw [trie]
        change TrieOutcome (chooseBranches program keys) rows s
        cases keyEq : keys with
        | nil =>
          have someKey := key_of_row (row := first) (rows := rows) List.mem_cons_self
          change first.head? ∈ keys at someKey
          rw [keyEq] at someKey
          simp at someKey
        | cons key moreKeys =>
          cases moreKeys with
          | nil => exact branch key (by simp [keyEq]) s scratch
          | cons key' qs =>
            let field := Cantor.unpair (s pl)
            let next := controls s field.2 (s sel + field.1)
            have load : Executes (read sel) s .normal next :=
              run_read (by decide) (by decide) s scratch.tokZero scratch.auxZero
            obtain ⟨selected, residual, choose⟩ :=
              selectBranch_exists (key :: key' :: qs) (next sel) (by simp)
            have selectedKey : selected ∈ keys := keyEq.symm ▸ selectBranch_mem choose
            let start := controls s field.2 residual
            have startEq : next.set sel residual = start := Store.set_set _ _ _ _
            have startReady : ClearScratch start := (scratch.setPL _).setSel _
            obtain ⟨row, mem, p, v, limit, exec⟩ := branch selected selectedKey start startReady
            have boundField : field.2 ≤ s pl := by
              have h := Cantor.right_le field.1 field.2
              simpa only [field, Cantor.pair_unpair] using h
            have pending : start pl = field.2 := by simp [start, controls, Store.set, pl, sel]
            have result : controls (runPattern row start) p v = controls (runPattern row s) p v := by
              change controls (runPattern row (controls s field.2 residual)) p v = _
              rw [runPattern_controls, controls_override]
            have selectedProgram :
                selectBranch ((key :: key' :: qs).map fun k => block (program k)) (next sel) =
                  some (block (program selected), residual) := by
              rw [selectBranch_map, choose]
              rfl
            have runSelected : Executes (block (program selected)) (next.set sel residual) .normal
                (controls (runPattern row start) p v) := by
              rw [startEq]
              exact exec.block
            have dispatched := run_dispatch _ next selectedProgram runSelected
            rw [result] at dispatched
            have bounded : p ≤ field.2 := pending ▸ limit
            exact ⟨row, mem, p, v, Nat.le_trans bounded boundField, .cons load (.cons dispatched .nil)⟩

/-- Serialize a finite stack of selector readings, with arbitrary
pending input preserved at the bottom. -/
def encodeFields : List Nat → Nat → Nat
  | [], tail => tail
  | x :: xs, tail => Cantor.pair x (encodeFields xs tail)

set_option maxHeartbeats 5000000 in
theorem execute_trie_row (fuel : Nat) (rows : List (List Pattern))
    (adequate : ∀ row ∈ rows, row.length ≤ fuel) (row : List Pattern) (member : row ∈ rows) :
    ∃ fields : List Nat, ∀ s tail, ClearScratch s →
      LineRuns (trie fuel rows) (controls s (encodeFields fields tail) 0) (controls (runPattern row s) tail 0) := by
  induction fuel generalizing rows row with
  | zero =>
    have empty : row = [] := by simpa using adequate row member
    subst row
    exact ⟨[], fun _ _ _ => .nil⟩
  | succ fuel ih =>
    cases rows with
    | nil => simp at member
    | cons first rest =>
      cases rest with
      | nil =>
        have eq : row = first := List.mem_singleton.mp member
        subst row
        refine ⟨[], fun s tail scratch => ?_⟩
        have run := runPattern_compiled first (controls s tail 0) ((scratch.setPL _).setSel _)
        rw [runPattern_controls] at run
        exact run
      | cons second more =>
        let rows := first :: second :: more
        let keys := branchKeys rows
        let program := trieBranch (trie fuel) rows
        have keyMem : row.head? ∈ keys := key_of_row member
        have branch :
            ∃ fields : List Nat, ∀ s tail, ClearScratch s →
              LineRuns (program row.head?) (controls s (encodeFields fields tail) 0)
                (controls (runPattern row s) tail 0) := by
          cases row with
          | nil => exact ⟨[], fun _ _ _ => .nil⟩
          | cons head suffix =>
            let subrows := branchTail (some head) rows
            have enough : ∀ r ∈ subrows, r.length ≤ fuel := by
              intro r h
              have hBound := adequate _ (branchTail_mem.mp h)
              simp only [List.length_cons] at hBound
              omega
            obtain ⟨fields, chosen⟩ := ih subrows enough suffix (branchTail_mem.mpr member)
            refine ⟨fields, fun s tail scratch => ?_⟩
            let start := controls s (encodeFields fields tail) 0
            have exec := head.run start ((scratch.setPL _).setSel _)
            have step : head.effect start = controls (head.effect s) (encodeFields fields tail) 0 := by
              simpa only [runPattern] using runPattern_controls [head] s (encodeFields fields tail) 0
            rw [step] at exec
            exact .cons exec (chosen _ _ (head.ready scratch))
        obtain ⟨fields, executes⟩ := branch
        rw [trie]
        change ∃ fs : List Nat, ∀ s tail, ClearScratch s →
          LineRuns (chooseBranches program keys) (controls s (encodeFields fs tail) 0)
            (controls (runPattern row s) tail 0)
        cases shape : keys with
        | nil => rw [shape] at keyMem; simp at keyMem
        | cons fst cs =>
          cases cs with
          | nil =>
            have h : row.head? = fst := by simpa [shape] using keyMem
            rw [h] at executes
            exact ⟨fields, executes⟩
          | cons snd cs =>
            obtain ⟨index, inside, code⟩ := List.mem_iff_getElem.mp keyMem
            have choice : selectBranch keys index = some (row.head?, 0) := by
              rw [selectBranch_exact keys index inside, code]
            rw [shape] at choice
            refine ⟨index :: fields, fun s tail scratch => ?_⟩
            let pending := encodeFields fields tail
            let start := controls s (Cantor.pair index pending) 0
            let next := controls s pending index
            have hPL : start pl = Cantor.pair index pending := by simp [start, controls, Store.set, pl, sel]
            have hSEL : start sel = 0 := Store.get_set _ _ _
            have readRun : Executes (read sel) start .normal next := by
              have ready := (scratch.setPL (Cantor.pair index pending)).setSel 0
              have load := read_pair (dst := sel) (by decide) (by decide) start
                ready.tokZero ready.auxZero index pending hPL
              rw [hSEL, Nat.zero_add] at load
              change Executes (read sel) start .normal (controls start pending index) at load
              change Executes (read sel) start .normal (controls (controls s (Cantor.pair index pending) 0) pending index) at load
              rwa [controls_override] at load
            have selection : selectBranch ((fst :: snd :: cs).map fun k => block (program k)) (next sel) =
                some (block (program row.head?), 0) := by
              rw [selectBranch_map, show next sel = index from Store.get_set _ _ _, choice]
              rfl
            have branchRun : Executes (block (program row.head?)) (next.set sel 0)
                .normal (controls (runPattern row s) tail 0) := by
              have same : next.set sel 0 = controls s pending 0 := Store.set_set _ _ _ _
              rw [same]
              exact (executes s tail scratch).block
            exact .cons readRun (.cons (run_dispatch _ next selection branchRun) .nil)

theorem foldMaximum (xs : List (List Pattern)) (bound : Nat) :
    bound ≤ xs.foldl (fun n p => max n p.length) bound ∧
      ∀ row ∈ xs, row.length ≤ xs.foldl (fun n p => max n p.length) bound := by
  induction xs generalizing bound with
  | nil => simp
  | cons p ps ih =>
    have h := ih (max bound p.length)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h.1, ?_⟩
    intro row mem
    rcases List.mem_cons.mp mem with rfl | rest
    · exact Nat.le_trans (Nat.le_max_right _ _) h.1
    · exact h.2 row rest

theorem literalRows_run (s : Store) (ready : ClearScratch s) :
    TrieOutcome compiledRows (rows.map rowPattern) s :=
  run_trie _ _ (by decide) (foldMaximum _ 0).2 s ready

theorem literalRows_cover {equation : Equation} (member : equation ∈ rows) :
    ∃ fields : List Nat, ∀ s tail, ClearScratch s →
      LineRuns compiledRows (controls s (encodeFields fields tail) 0)
        (controls (runPattern (rowPattern equation) s) tail 0) :=
  execute_trie_row _ _ (foldMaximum _ 0).2 _ (List.mem_map.mpr ⟨equation, member, rfl⟩)

end PalomarI3380.Compiler.Source
