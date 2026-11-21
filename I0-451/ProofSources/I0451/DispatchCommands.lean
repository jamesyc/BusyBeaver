module
public import I0451.OperandReading

/-! The literal dispatch chain consumes the selector one unit at a time.
The terminal case receives the residual selector used as AX's mode. -/
@[expose] public section
namespace I0451.Runtime

theorem putRegister_read {α : Type} (s : Fin 9 → α) (r : Fin 9) : putRegister s r (s r) = s := by
  funext j
  by_cases h : j = r <;> simp [putRegister, h]

theorem putRegister_overwrite {α : Type} (s : Fin 9 → α) (r : Fin 9) (v w : α) :
    putRegister (putRegister s r v) r w = putRegister s r w := by
  funext j
  by_cases h : j = r <;> simp [putRegister, h]

/-- A command boundary can finish normally or halt. Its internal
break and continue signals are resolved before it returns. -/
def CommandSignal (signal : Signal) : Prop := signal = .normal ∨ signal = .halt

inductive DispatchTree where
  | command (entry : Cursor)
  | choose (entry test nextBranch first : Cursor) (rest : DispatchTree)

def DispatchTree.entry : DispatchTree → Cursor
  | .command c | .choose c _ _ _ _ => c

def DispatchTree.select : DispatchTree → Nat → Cursor × Nat
  | .command c, n => (c, n)
  | .choose _ _ _ first _, 0 => (first, 0)
  | .choose _ _ _ _ rest, n + 1 => rest.select n

def DispatchTree.verified : DispatchTree → Prop
  | .command _ => True
  | .choose entry test nextBranch first rest =>
    outgoing entry false = some (.branch test) ∧
    outgoing entry true = some (.branch first) ∧
    outgoing test false = some (.instruction (.dec axiomIndex)) ∧
    outgoing test true = some (.branch nextBranch) ∧
    outgoing nextBranch false = some (.branch rest.entry) ∧
    outgoing nextBranch true = some (.instruction (.break 0)) ∧ rest.verified

instance (tree : DispatchTree) : Decidable tree.verified := by
  cases tree with
  | command _ => exact isTrue trivial
  | choose _ _ _ _ rest =>
    letI := instDecidableVerified rest
    unfold DispatchTree.verified
    infer_instance

private theorem choose_normal {entry test recurse : Cursor} {rest : Edge}
    {s post : Registers} {n : Nat}
    (testEdge : outgoing entry false = some (.branch test))
    (selectEdge : outgoing test false = some (.instruction (.dec axiomIndex)))
    (recurseEdge : outgoing test true = some (.branch recurse))
    (callEdge : outgoing recurse false = some rest)
    (skipEdge : outgoing recurse true = some (.instruction (.break 0)))
    (positive : s axiomIndex = n + 1)
    (called : Executes rest (putRegister s axiomIndex n) .normal post) :
    Executes (.branch entry) s .normal post := by
  have skip : Executes (.branch recurse) (putRegister s axiomIndex n) (.break 0) post :=
    .rightExit callEdge skipEdge called (.break 0 _) rfl
  have decided : Executes (.branch test) s (.break 0) post :=
    .rightExit selectEdge recurseEdge (.decPositive axiomIndex s n positive) skip rfl
  exact .leftExit testEdge decided rfl

private theorem choose_halt {entry test recurse : Cursor} {rest : Edge}
    {s post : Registers} {n : Nat}
    (testEdge : outgoing entry false = some (.branch test))
    (selectEdge : outgoing test false = some (.instruction (.dec axiomIndex)))
    (recurseEdge : outgoing test true = some (.branch recurse))
    (callEdge : outgoing recurse false = some rest)
    (positive : s axiomIndex = n + 1)
    (called : Executes rest (putRegister s axiomIndex n) .halt post) :
    Executes (.branch entry) s .halt post := by
  have run : Executes (.branch recurse) (putRegister s axiomIndex n) .halt post :=
    .leftExit callEdge called rfl
  have decided : Executes (.branch test) s .halt post :=
    .rightExit selectEdge recurseEdge (.decPositive axiomIndex s n positive) run rfl
  exact .leftExit testEdge decided rfl

theorem DispatchTree.run {tree : DispatchTree} (checked : tree.verified)
    (s finish : Registers) {signal : Signal} (boundary : CommandSignal signal)
    (command : Executes (.branch (tree.select (s axiomIndex)).1)
      (putRegister s axiomIndex (tree.select (s axiomIndex)).2) signal finish) :
    Executes (.branch tree.entry) s signal finish := by
  induction tree generalizing s with
  | command c =>
    simpa only [DispatchTree.select, DispatchTree.entry, putRegister_read] using command
  | choose entry test recurse first rest ih =>
    obtain ⟨testEdge, firstEdge, selectEdge, recurseEdge, callEdge, skipEdge, inner⟩ := checked
    cases count : s axiomIndex with
    | zero =>
      simp only [count, DispatchTree.select] at command
      have initial : putRegister s axiomIndex 0 = s := by
        rw [← count, putRegister_read]
      rw [initial] at command
      have skip : Executes (.branch test) s .normal s :=
        .leftExit selectEdge (.decZero axiomIndex s count) rfl
      have normalRight : signal.rightExit = some signal := by
        rcases boundary with rfl | rfl <;> rfl
      exact .rightExit testEdge firstEdge skip command normalRight
    | succ n =>
      let reduced := putRegister s axiomIndex n
      have ready : reduced axiomIndex = n := putRegister_at s axiomIndex n
      simp only [count, DispatchTree.select] at command
      have recurse : Executes (.branch rest.entry) reduced signal finish := by
        apply ih inner reduced
        simpa only [ready, reduced, putRegister_overwrite] using command
      rcases boundary with rfl | rfl
      · exact choose_normal testEdge selectEdge recurseEdge callEdge skipEdge count recurse
      · exact choose_halt testEdge selectEdge recurseEdge callEdge count recurse

def mpCursor : Cursor := ⟨35, true, true⟩
def dropCursor : Cursor := ⟨84, true, false⟩
def nipCursor : Cursor := ⟨125, true, false⟩
def extraCursor : Cursor := ⟨155, true, false⟩
def axCursor : Cursor := ⟨163, false, true⟩

def commandDispatch : DispatchTree :=
  .choose ⟨21, true, true⟩ ⟨34, false, true⟩ ⟨50, true, false⟩ mpCursor
    (.choose ⟨66, false, true⟩ ⟨83, false, false⟩ ⟨100, true, false⟩ dropCursor
      (.choose ⟨114, false, true⟩ ⟨124, false, false⟩ ⟨137, true, false⟩ nipCursor
        (.choose ⟨147, false, true⟩ ⟨154, false, false⟩ ⟨159, true, false⟩ extraCursor
          (.command axCursor))))

theorem commandDispatch_checked : commandDispatch.verified := by decide +kernel

theorem commandDispatch_select (n : Nat) :
    commandDispatch.select n =
      match n with
      | 0 => (mpCursor, 0)
      | 1 => (dropCursor, 0)
      | 2 => (nipCursor, 0)
      | 3 => (extraCursor, 0)
      | k + 4 => (axCursor, k) := by
  rcases n with _ | _ | _ | _ | n <;> rfl

def beforeDispatch (s : Registers) : Registers :=
  readResult parameterOne (readResult axiomIndex (afterLoad s))

theorem main_exec {s finish : Registers} {sig : Signal}
    (s1 : s scratchOne = 0) (s2 : s scratchTwo = 0)
    (boundary : CommandSignal sig)
    (run : Executes (.branch commandDispatch.entry) (beforeDispatch s) sig finish) :
    Executes mainEdge s sig finish := by
  let read := afterLoad s
  let op := readResult axiomIndex read
  have readPreserves (r : Fin 9) (pl : r ≠ proofList) (np : r ≠ nextProof) : read r = s r := by
    unfold read afterLoad
    split <;> simp [putRegister, pl, np]
  have readOne : read scratchOne = 0 := (readPreserves _ (by decide) (by decide)).trans s1
  have readTwo : read scratchTwo = 0 := (readPreserves _ (by decide) (by decide)).trans s2
  have opPreserves (r : Fin 9) (pl : r ≠ proofList) (ax : r ≠ axiomIndex) : op r = read r := by
    simp [op, readResult, readFrom, putRegister, pl, ax]
  have opOne : op scratchOne = 0 := (opPreserves _ (by decide) (by decide)).trans readOne
  have opTwo : op scratchTwo = 0 := (opPreserves _ (by decide) (by decide)).trans readTwo
  have signal : sig.rightExit = some sig := by
    rcases boundary with rfl | rfl <;> rfl
  have readOp := Executes.rightExit (cursor := ⟨13, true, true⟩) (by decide +kernel)
    (by decide +kernel) (literal_read_operand op opOne opTwo) run signal
  have readSelector := Executes.rightExit (cursor := ⟨9, true, true⟩) (by decide +kernel)
    (by decide +kernel) (literal_read_selector read readOne readTwo) readOp signal
  exact .rightExit main_load_branch (by decide +kernel) (literal_candidate_loader s s1) readSelector signal

end I0451.Runtime
