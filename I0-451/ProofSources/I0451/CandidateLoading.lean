module
public import I0451.CounterLoops

/-! The actual opening block of the 451-state program. Its branches
either peel the nonempty queue delimiter or load the next candidate
using the scratch register. -/
@[expose] public section
namespace I0451.Runtime

def nextProof : Fin 9 := 0
def topWff : Fin 9 := 1
def wffStack : Fin 9 := 2
def axiomIndex : Fin 9 := 3
def parameterOne : Fin 9 := 4
def parameterTwo : Fin 9 := 5
def scratchOne : Fin 9 := 6
def scratchTwo : Fin 9 := 7
def proofList : Fin 9 := 8

def setupCursor : Cursor := ⟨8, false, true⟩

namespace CandidateInput

def copyCursor : Cursor := ⟨16, false, true⟩
def copyLoop : Cursor := ⟨26, true, false⟩
def copyIncrements : Cursor := ⟨40, false, true⟩
def restoreCursor : Cursor := ⟨27, false, true⟩
def restoreLoop : Cursor := ⟨42, true, false⟩
def loadCursor : Cursor := ⟨11, true, false⟩
def incrementCursor : Cursor := ⟨17, true, true⟩
def testCursor : Cursor := ⟨10, false, false⟩

end CandidateInput

open CandidateInput

theorem main_load_branch : outgoing rootCursor false = some (.branch setupCursor) := by decide +kernel

private theorem copyCandidate (s : Registers) :
    Executes (.branch copyCursor) s .normal
      (putRegister (addAt (fun j => j == proofList || j == scratchOne) (s nextProof) s) nextProof 0) := by
  apply while_add (block := copyLoop) (body := .branch copyIncrements)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro regs
    exact increment_two (by decide) (by decide +kernel) (by decide +kernel) regs

private theorem restoreCandidate (s : Registers) :
    Executes (.branch restoreCursor) s .normal
      (putRegister (addAt (· == nextProof) (s scratchOne) s) scratchOne 0) := by
  apply while_add (block := restoreLoop) (body := .instruction (.inc nextProof))
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact increment_one nextProof

private theorem loadCandidate (s : Registers) (empty : s proofList = 0) (clean : s scratchOne = 0) :
    Executes (.branch loadCursor) s .normal
      (putRegister (putRegister s proofList (s nextProof)) nextProof (s nextProof + 1)) := by
  let copied := putRegister (addAt (fun j => j == proofList || j == scratchOne) (s nextProof) s) nextProof 0
  let restored := putRegister (addAt (· == nextProof) (copied scratchOne) copied) scratchOne 0
  have copy := copyCandidate s
  have restore := restoreCandidate copied
  have increment := Executes.inc nextProof restored
  have same : putRegister restored nextProof (restored nextProof + 1) =
      putRegister (putRegister s proofList (s nextProof)) nextProof (s nextProof + 1) := by
    funext j
    have nz1 : scratchOne ≠ nextProof := by decide
    have nz2 : scratchOne ≠ proofList := by decide
    have nz3 : proofList ≠ nextProof := by decide
    by_cases q : j = nextProof
    · subst j
      simp [restored, copied, addAt, putRegister, Ne.symm nz1, nz1, clean]
    · by_cases r : j = scratchOne
      · subst j
        simp [restored, putRegister, nz1, nz2, clean]
      · by_cases t : j = proofList
        · subst j
          simp [restored, copied, addAt, putRegister, nz3, Ne.symm nz2, empty]
        · simp [restored, copied, addAt, putRegister, q, r, t]
  rw [← same]
  exact executes_sequence (by decide +kernel) (by decide +kernel) copy
    (executes_sequence (root := incrementCursor) (by decide +kernel) (by decide +kernel) restore increment)

def afterLoad (s : Registers) : Registers :=
  if s proofList = 0 then
    putRegister (putRegister s proofList (s nextProof)) nextProof (s nextProof + 1)
  else putRegister s proofList (s proofList - 1)

theorem literal_candidate_loader (s : Registers) (clean : s scratchOne = 0) :
    Executes (.branch setupCursor) s .normal (afterLoad s) := by
  unfold afterLoad
  apply if_zero (test := testCursor) (body := .branch loadCursor)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact fun empty => loadCandidate s empty clean

end I0451.Runtime
