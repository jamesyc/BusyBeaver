module
public import I0451.DispatchCommands
public import I0451.SearchExecution

/-! The two reads at entry and dispatch are synchronized with the
scheduler's decoding of the next command. -/
@[expose] public section
namespace I0451.Runtime

open I0451.Logic M6.Source.Cantor

def nextIndex (s : SearchState ProofStore) : Nat :=
  if s.queued = 0 then s.nextCandidate + 1 else s.nextCandidate

def payload (s : SearchState ProofStore) : Nat :=
  if s.queued = 0 then s.nextCandidate else s.queued - 1

def commandRegisters (next queue selector : Nat) (p : ProofStore) : Registers :=
  putRegister (searchRegisters ⟨next, queue, p⟩) axiomIndex selector

theorem commandRegisters_none (n q : Nat) (p : ProofStore) :
    commandRegisters n q 0 p = searchRegisters ⟨n, q, p⟩ :=
  putRegister_read _ _

theorem index_cases (i : Fin 9) :
    i = nextProof ∨ i = topWff ∨ i = wffStack ∨ i = axiomIndex ∨ i = parameterOne ∨
      i = parameterTwo ∨ i = scratchOne ∨ i = scratchTwo ∨ i = proofList := by
  unfold nextProof topWff wffStack axiomIndex parameterOne parameterTwo scratchOne scratchTwo proofList
  omega

@[simp] theorem searchRegisters_nextProof (s : SearchState ProofStore) : searchRegisters s nextProof = s.nextCandidate := rfl

@[simp] theorem searchRegisters_topWff (s : SearchState ProofStore) : searchRegisters s topWff = s.store.top := rfl

@[simp] theorem searchRegisters_wffStack (s : SearchState ProofStore) : searchRegisters s wffStack = s.store.stack := rfl

@[simp] theorem searchRegisters_axiomIndex (s : SearchState ProofStore) : searchRegisters s axiomIndex = 0 := rfl

@[simp] theorem searchRegisters_parameterOne (s : SearchState ProofStore) : searchRegisters s parameterOne = s.store.operand := rfl

@[simp] theorem searchRegisters_parameterTwo (s : SearchState ProofStore) : searchRegisters s parameterTwo = s.store.cache := rfl

@[simp] theorem searchRegisters_scratchOne (s : SearchState ProofStore) : searchRegisters s scratchOne = 0 := rfl

@[simp] theorem searchRegisters_scratchTwo (s : SearchState ProofStore) : searchRegisters s scratchTwo = 0 := rfl

@[simp] theorem searchRegisters_proofList (s : SearchState ProofStore) : searchRegisters s proofList = s.queued := rfl

theorem beforeDispatch_eq (s : SearchState ProofStore) :
    beforeDispatch (searchRegisters s) =
      let header := decode (payload s)
      let operands := decode header.2
      commandRegisters (nextIndex s) operands.2 header.1
        {s.store with operand := s.store.operand + operands.1} := by
  have rd : (searchRegisters s) proofList = s.queued := rfl
  simp only [beforeDispatch, afterLoad, rd, searchRegisters_nextProof]
  by_cases fresh : s.queued = 0
  · simp only [ite_eq_left fresh, nextIndex, payload]
    funext j
    rcases index_cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact Nat.zero_add _
  · simp only [ite_eq_right fresh, nextIndex, payload]
    funext j
    rcases index_cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact Nat.zero_add _

theorem dispatch_to {next queue selector : Nat} {store : ProofStore} {sig : Signal}
    {finish : Registers} (valid : CommandSignal sig)
    (run : Executes (.branch (commandDispatch.select selector).1)
      (commandRegisters next queue (commandDispatch.select selector).2 store) sig finish) :
    Executes (.branch commandDispatch.entry) (commandRegisters next queue selector store) sig finish := by
  apply DispatchTree.run commandDispatch_checked _ _ valid
  simpa only [commandRegisters, putRegister_at, putRegister_overwrite] using run

theorem step_decoded (exec : CommandEval ProofStore) (s : SearchState ProofStore) :
    s.step exec = ((exec (unpackCommand (payload s)).1 s.store).map
      fun store => ⟨nextIndex s, (unpackCommand (payload s)).2, store⟩) := by
  by_cases fresh : s.queued = 0 <;>
    simp [SearchState.step, payload, nextIndex, fresh]

end I0451.Runtime
