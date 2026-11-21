module
public import I0451.DispatchCommands
public import I0451.PairingLoops

/-! The literal stack-push routine and its use by DROP. These proofs use
the reusable counter contracts at graph entry points read from the
451-state decoder. -/
@[expose] public section
namespace I0451.Runtime

open M6.Source.Cantor

def pairEntry : Cursor := ⟨130, true, false⟩
def fillEntry : Cursor := ⟨142, false, true⟩
def fillLoop : Cursor := ⟨149, true, false⟩
def fillBody : Cursor := ⟨157, false, true⟩
def pairTest : Cursor := ⟨143, true, true⟩
def pairRepeat : Cursor := ⟨150, true, true⟩
def rotateEntry : Cursor := ⟨158, false, true⟩

private theorem fill_stack_pair (s : Registers) :
    Executes (.branch fillEntry) s .normal (fillPair scratchOne topWff scratchTwo s) := by
  apply while_add (block := fillLoop) (body := .branch fillBody)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide
  · intro r
    exact increment_two (by decide) (by decide +kernel) (by decide +kernel) r

private theorem rotate_stack_pair (s : Registers) :
    Executes (.branch rotateEntry) s .normal (rotatePair scratchOne topWff scratchTwo s) := by
  have transfer := move_one (entry := ⟨162, true, false⟩) (loop := ⟨152, true, true⟩)
    (source := scratchOne) (target := topWff) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (putRegister s scratchTwo (s scratchTwo + 1))
  exact executes_sequence (by decide +kernel) (by decide +kernel) (.inc scratchTwo s) transfer

theorem literal_stack_pair (s : Registers) :
    Executes (.branch pairEntry) s .normal (pairedRegisters scratchOne topWff scratchTwo s) := by
  exact executes_pair (test := pairTest) (cycle := pairRepeat) (fill := .branch fillEntry)
    (move := .branch rotateEntry) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) fill_stack_pair rotate_stack_pair s

def stackPushCursor : Cursor := ⟨108, false, false⟩
def pushRest : Cursor := ⟨122, true, false⟩
def pushPair : Cursor := ⟨135, false, true⟩

def pushResult (s : Registers) : Registers :=
  putRegister (putRegister s topWff 0) wffStack (pair (s topWff) (s wffStack))

/-- Saving a formula preserves the existing proof stack beneath it and
clears the accumulator. -/
theorem literal_stack_push (s : Registers) (firstZero : s scratchOne = 0) (secondZero : s scratchTwo = 0) :
    Executes (.branch stackPushCursor) s .normal (pushResult s) := by
  let a := transferOne topWff scratchOne s
  let b := transferOne wffStack topWff a
  let c := pairedRegisters scratchOne topWff scratchTwo b
  let d := transferOne scratchTwo wffStack c
  have first := move_one (entry := ⟨69, false, false⟩) (loop := ⟨89, true, false⟩)
    (source := topWff) (target := scratchOne) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) s
  have second := move_one (entry := ⟨145, false, false⟩) (loop := ⟨152, true, false⟩)
    (source := wffStack) (target := topWff) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) a
  have third := literal_stack_pair b
  have fourth := move_one (entry := ⟨129, true, true⟩) (loop := ⟨141, true, true⟩)
    (source := scratchTwo) (target := wffStack) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) c
  have rest := executes_sequence (root := pushRest) (by decide +kernel) (by decide +kernel)
    (executes_sequence (root := pushPair) (by decide +kernel) (by decide +kernel) second third) fourth
  have ran : Executes (.branch stackPushCursor) s .normal d :=
    executes_sequence (by decide +kernel) (by decide +kernel) first rest
  have same : d = pushResult s := by
    funext j
    have fs : s 6 = 0 := firstZero
    have ss : s 7 = 0 := secondZero
    by_cases tw : j = topWff
    · subst j
      simp [d, c, b, a, transferOne, pairedRegisters, addAt, putRegister, pushResult, topWff,
        wffStack, scratchOne, scratchTwo]
    · by_cases ws : j = wffStack
      · subst j
        simp [d, c, b, a, transferOne, pairedRegisters, addAt, putRegister, pushResult, topWff,
          wffStack, scratchOne, scratchTwo, fs, ss]
      · by_cases s₁ : j = scratchOne
        · subst j
          simp [d, c, b, a, transferOne, pairedRegisters, addAt, putRegister, pushResult, topWff,
            wffStack, scratchOne, scratchTwo, fs]
        · by_cases s₂ : j = scratchTwo
          · subst j
            simp [d, transferOne, putRegister, pushResult, topWff, wffStack, scratchTwo, ss]
          · simp [d, c, b, a, transferOne, pairedRegisters, addAt, putRegister, pushResult, tw, ws, s₁, s₂]
  rw [same] at ran
  exact ran

def dropResult (s : Registers) : Registers :=
  putRegister (pushResult s) topWff (s parameterTwo)

/-- DROP copies the current cache into the accumulator, saving the old
accumulator on the proof stack. -/
theorem literal_drop (s : Registers) (firstZero : s scratchOne = 0) (secondZero : s scratchTwo = 0) :
    Executes (.branch dropCursor) s .normal (dropResult s) := by
  let pushed := pushResult s
  let copied := putRegister (addAt (fun j => j == scratchOne || j == topWff)
    (pushed parameterTwo) pushed) parameterTwo 0
  let restored := transferOne scratchOne parameterTwo copied
  have copy : Executes (.branch ⟨115, true, false⟩) pushed .normal copied := by
    apply while_add (block := ⟨127, true, true⟩) (body := .branch ⟨140, false, true⟩)
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide
    · intro r
      exact increment_two (by decide) (by decide +kernel) (by decide +kernel) r
  have restore := move_one (entry := ⟨102, true, true⟩) (loop := ⟨116, true, true⟩)
    (source := scratchOne) (target := parameterTwo) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) copied
  have ready := executes_sequence (root := ⟨101, false, true⟩) (by decide +kernel) (by decide +kernel)
    (literal_stack_push s firstZero secondZero) copy
  have ran : Executes (.branch dropCursor) s .normal restored :=
    executes_sequence (by decide +kernel) (by decide +kernel) ready restore
  have same : restored = dropResult s := by
    funext j
    have fs : s 6 = 0 := firstZero
    by_cases ht : j = topWff
    · subst j
      simp [restored, copied, pushed, transferOne, addAt, putRegister, dropResult,
        pushResult, topWff, parameterTwo, scratchOne, wffStack]
    · by_cases hp : j = parameterTwo
      · subst j
        simp [restored, copied, pushed, transferOne, addAt, putRegister, dropResult,
          pushResult, topWff, parameterTwo, scratchOne, wffStack, fs]
      · by_cases hs : j = scratchOne
        · subst j
          simp [restored, transferOne, putRegister, dropResult, pushResult, topWff,
            parameterTwo, scratchOne, wffStack, fs]
        · simp [restored, copied, transferOne, addAt, putRegister, dropResult, ht, hp, hs, pushed]
  rw [same] at ran
  exact ran

end I0451.Runtime
