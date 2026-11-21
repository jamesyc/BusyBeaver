module
public import I0451.CandidateLoading
public import I0451.Logic.Formula

/-! The operand readers in the literal graph. The shared unpair routine
walks the Cantor diagonals; the two readers move the first component to
different destination registers. -/
@[expose] public section
namespace I0451.Runtime

open M6.Source.Cantor

def unpairCursor : Cursor := ⟨29, false, false⟩
def unpairLoop : Cursor := ⟨44, true, false⟩
def unpairBody : Cursor := ⟨61, false, true⟩
def unpairTest : Cursor := ⟨80, true, false⟩
def unpairGuard : Cursor := ⟨98, false, true⟩
def shiftCursor : Cursor := ⟨99, true, true⟩
def shiftLoop : Cursor := ⟨89, true, true⟩
def unpackRestore : Cursor := ⟨18, false, false⟩
def restoreList : Cursor := ⟨30, true, false⟩
def restoreLoop : Cursor := ⟨45, true, true⟩

def readSelector : Cursor := ⟨12, false, true⟩
def readOperand : Cursor := ⟨20, false, true⟩

private theorem scratchDistinct : scratchOne ≠ scratchTwo := by decide
private theorem listDistinctOne : proofList ≠ scratchOne := by decide
private theorem listDistinctTwo : proofList ≠ scratchTwo := by decide

private theorem shiftScratch (s : Registers) :
    Executes (.branch shiftCursor) s .normal
      (putRegister (addAt (· == scratchOne) (s scratchTwo) s) scratchTwo 0) := by
  apply while_add (block := shiftLoop) (body := .instruction (.inc scratchOne))
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact increment_one scratchOne

def advanceScratch (s : Registers) : Registers :=
  let xy := advance (s scratchOne, s scratchTwo)
  putRegister (putRegister s scratchOne xy.1) scratchTwo xy.2

private theorem advance_exec (s : Registers) : Executes (.branch unpairBody) s .normal (advanceScratch s) := by
  let added := putRegister s scratchTwo (s scratchTwo + 1)
  let shifted := putRegister (addAt (· == scratchOne) (added scratchTwo) added) scratchTwo 0
  have c : Executes (.branch unpairTest) added .normal
      (if added scratchOne = 0 then shifted else putRegister added scratchOne (added scratchOne - 1)) :=
    if_zero (test := unpairGuard) (body := .branch shiftCursor)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun _ => shiftScratch added)
  have all := executes_sequence (root := unpairBody) (by decide +kernel) (by decide +kernel)
    (Executes.inc scratchTwo s) c
  have same : (if added scratchOne = 0 then shifted else putRegister added scratchOne (added scratchOne - 1))
      = advanceScratch s := by
    cases x : s scratchOne with
    | zero =>
      funext j
      by_cases h : j = scratchOne
      · subst j
        simp [shifted, added, addAt, putRegister, scratchDistinct, advanceScratch, advance, x]
      · by_cases k : j = scratchTwo
        · simp [k, shifted, added, putRegister, scratchDistinct, advanceScratch, advance, x]
        · simp [shifted, added, addAt, putRegister, h, k, scratchDistinct, advanceScratch, advance, x]
    | succ n =>
      funext j
      by_cases h : j = scratchOne
      · simp [h, added, putRegister, scratchDistinct, advanceScratch, advance, x]
      · by_cases k : j = scratchTwo
        · simp [k, added, putRegister, scratchDistinct, Ne.symm scratchDistinct, advanceScratch, advance, x]
        · simp [added, putRegister, h, k, scratchDistinct, advanceScratch, advance, x]
  rw [same] at all
  exact all

def unpairPost (source : Fin 9) (n : Nat) (s : Registers) : Registers :=
  let xy := decode (pair (s scratchOne) (s scratchTwo) + n)
  putRegister (putRegister (putRegister s source 0) scratchOne xy.1) scratchTwo xy.2

private theorem scratch_steps (s : Registers) :
    (advanceScratch s scratchOne, advanceScratch s scratchTwo) = advance (s scratchOne, s scratchTwo) := by
  simp [advanceScratch, putRegister, scratchDistinct]

private theorem unpair_zero (source : Fin 9) (srcOne : source ≠ scratchOne)
    (srcTwo : source ≠ scratchTwo) (s : Registers) (empty : s source = 0) :
    unpairPost source 0 s = s := by
  funext j
  by_cases first : j = scratchOne
  · simp [unpairPost, decode_pair, putRegister, first, scratchDistinct]
  · by_cases second : j = scratchTwo
    · simp [unpairPost, decode_pair, second]
    · by_cases pl : j = source
      · simp [unpairPost, putRegister, pl, srcOne, srcTwo, empty]
      · simp [unpairPost, putRegister, first, second, pl]

private theorem unpair_succ (source : Fin 9) (srcOne : source ≠ scratchOne)
    (srcTwo : source ≠ scratchTwo) (n : Nat) (s : Registers) :
    unpairPost source (n + 1) s = unpairPost source n (advanceScratch (putRegister s source n)) := by
  let u := putRegister s source n
  have paired : pair (advanceScratch u scratchOne) (advanceScratch u scratchTwo) =
      pair (s scratchOne) (s scratchTwo) + 1 := by
    have change := pair_advance (u scratchOne, u scratchTwo)
    rw [← scratch_steps] at change
    simpa [u, putRegister, Ne.symm srcOne, Ne.symm srcTwo] using change
  have sum : pair (s scratchOne) (s scratchTwo) + (n + 1) =
      pair (advanceScratch u scratchOne) (advanceScratch u scratchTwo) + n := by
    rw [paired]
    omega
  funext j
  unfold unpairPost
  rw [sum]
  simp only [u]
  by_cases second : j = scratchTwo
  · simp [putRegister, second]
  · by_cases first : j = scratchOne
    · simp [putRegister, first]
    · by_cases pl : j = source
      · simp [putRegister, pl]
      · simp [putRegister, second, first, pl, advanceScratch]

/-- Run a literal Cantor-unpair loop from either input register.
The shared body is the verified scratch-pair successor. -/
theorem unpair_graph {entry loop : Cursor} {source : Fin 9}
    (dec : outgoing entry false = some (.instruction (.dec source)))
    (body : outgoing entry true = some (.branch loop))
    (advance : outgoing loop false = some (.branch unpairBody))
    (repeatLoop : outgoing loop true = some (.instruction (.restart 1)))
    (first : source ≠ scratchOne) (second : source ≠ scratchTwo) (s : Registers) :
    Executes (.branch entry) s .normal (unpairPost source (s source) s) := by
  apply while_effect dec body advance repeatLoop (update := advanceScratch) (post := unpairPost source)
  · exact advance_exec
  · intro regs
    simp [advanceScratch, putRegister, first, second]
  · exact unpair_zero source first second
  · intro n regs _
    exact unpair_succ source first second n regs

theorem unpair_prooflist (s : Registers) :
    Executes (.branch unpairCursor) s .normal (unpairPost proofList (s proofList) s) :=
  unpair_graph (loop := unpairLoop) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) listDistinctOne listDistinctTwo s

private theorem restoreComponent (s : Registers) :
    Executes (.branch restoreList) s .normal
      (putRegister (addAt (· == proofList) (s scratchTwo) s) scratchTwo 0) := by
  apply while_add (block := restoreLoop) (body := .instruction (.inc proofList))
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact increment_one proofList

def readFrom (source target : Fin 9) (s : Registers) : Registers :=
  let xy := decode (s source)
  putRegister (putRegister s source xy.2) target (s target + xy.1)

def readResult (target : Fin 9) := readFrom proofList target

theorem read_transfer {source target : Fin 9} (targetOne : target ≠ scratchOne)
    (targetTwo : target ≠ scratchTwo) (targetSource : target ≠ source)
    (sourceOne : source ≠ scratchOne) (sourceTwo : source ≠ scratchTwo)
    (s : Registers) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    transferOne scratchOne target (transferOne scratchTwo source
      (unpairPost source (s source) s)) = readFrom source target s := by
  let split := unpairPost source (s source) s
  have eval (j : Fin 9) : split j =
      (putRegister (putRegister (putRegister s source 0) scratchOne (decode (s source)).1)
        scratchTwo (decode (s source)).2) j := by
    simp [split, unpairPost, oneZero, twoZero, pair, triangle]
  change transferOne scratchOne target (transferOne scratchTwo source split) = _
  funext j
  by_cases jt : j = target
  · subst j
    simp [transferOne, eval, addAt, putRegister, targetOne, targetTwo, targetSource,
      scratchDistinct, Ne.symm sourceOne, readFrom]
  · by_cases jo : j = scratchOne
    · subst j
      simp [transferOne, putRegister, readFrom, Ne.symm targetOne, Ne.symm sourceOne, oneZero]
    · by_cases jt' : j = scratchTwo
      · subst j
        simp [transferOne, putRegister, addAt, jo, jt, Ne.symm sourceTwo, readFrom, twoZero]
      · by_cases jp : j = source
        · subst j
          simp [transferOne, eval, addAt, putRegister, sourceOne, sourceTwo,
            Ne.symm targetSource, readFrom]
        · simp [transferOne, eval, addAt, putRegister, jt, jo, jt', jp, readFrom]

private theorem execute_read {start move : Cursor} {target : Fin 9}
    (left : outgoing start false = some (.branch unpackRestore))
    (right : outgoing start true = some (.branch move))
    (moveFirst : ∀ s, Executes (.branch move) s .normal
      (transferOne scratchOne target s))
    (targetOne : target ≠ scratchOne) (targetTwo : target ≠ scratchTwo)
    (targetList : target ≠ proofList) (s : Registers)
    (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    Executes (.branch start) s .normal (readResult target s) := by
  let split := unpairPost proofList (s proofList) s
  let restored := transferOne scratchTwo proofList split
  have unpaired := unpair_prooflist s
  have restore := restoreComponent split
  have before := executes_sequence (root := unpackRestore) (by decide +kernel) (by decide +kernel)
    unpaired restore
  have moves := executes_sequence left right before (moveFirst restored)
  have eq := read_transfer targetOne targetTwo targetList listDistinctOne listDistinctTwo
    s oneZero twoZero
  simpa only [restored, split, eq, readResult] using moves

private theorem moveFirst {root loop : Cursor} {target : Fin 9}
    (dec : outgoing root false = some (.instruction (.dec scratchOne)))
    (body : outgoing root true = some (.branch loop))
    (inc : outgoing loop false = some (.instruction (.inc target)))
    (back : outgoing loop true = some (.instruction (.restart 1)))
    (distinct : target ≠ scratchOne) (s : Registers) :
    Executes (.branch root) s .normal (putRegister (addAt (· == target) (s scratchOne) s) scratchOne 0) :=
  while_add dec body inc back (· == target) (by simp [Ne.symm distinct]) (increment_one target) s

theorem literal_read_selector (s : Registers) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    Executes (.branch readSelector) s .normal (readResult axiomIndex s) := by
  apply execute_read (move := ⟨19, true, false⟩)
  · decide +kernel
  · decide +kernel
  · exact moveFirst (loop := ⟨32, true, true⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide)
  · decide
  · decide
  · decide
  · exact oneZero
  · exact twoZero

theorem literal_read_operand (s : Registers) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    Executes (.branch readOperand) s .normal (readResult parameterOne s) := by
  apply execute_read (move := ⟨33, true, false⟩)
  · decide +kernel
  · decide +kernel
  · exact moveFirst (loop := ⟨48, true, true⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide)
  · decide
  · decide
  · decide
  · exact oneZero
  · exact twoZero

end I0451.Runtime
