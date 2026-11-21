module
public import I0451.CommandInputs
public import I0451.Commands.AxiomExecution

/-! The ordinary literal command contracts compose with the scheduler.
The EXTRA formula codes enter through a single parameterized contract. -/
@[expose] public section
namespace I0451.Runtime

open I0451.Logic M6.Source.Cantor

private theorem mp_normal (n q : Nat) (s : ProofStore) :
    let after := if s.cache = imp s.top s.operand
      then ⟨s.operand, pair 0 s.stack, s.operand, 0⟩
      else ⟨0, s.stack, s.operand, 0⟩
    Executes (.branch mpCursor) (commandRegisters n q 0 s) .normal (searchRegisters ⟨n, q, after⟩) := by
  let regs := commandRegisters n q 0 s
  have run := literal_mp regs rfl rfl
  have output :
      mpResult regs =
        searchRegisters ⟨n, q, if s.cache = imp s.top s.operand then
          ⟨s.operand, pair 0 s.stack, s.operand, 0⟩ else ⟨0, s.stack, s.operand, 0⟩⟩ := by
    change (if s.cache = imp s.top s.operand then
        saveOperand (putRegister (putRegister regs topWff 0) parameterTwo 0)
        else putRegister (putRegister regs topWff 0) parameterTwo 0) = _
    split <;>
      funext j <;>
      rcases index_cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simpa only [output] using run

private theorem drop_normal (n q : Nat) (s : ProofStore) :
    Executes (.branch dropCursor) (commandRegisters n q 0 s) .normal
      (searchRegisters ⟨n, q, ⟨s.cache, pair s.top s.stack, s.operand, s.cache⟩⟩) := by
  have run := literal_drop (commandRegisters n q 0 s) rfl rfl
  have result : dropResult (commandRegisters n q 0 s) =
      searchRegisters ⟨n, q, ⟨s.cache, pair s.top s.stack, s.operand, s.cache⟩⟩ := by
    funext j
    rcases index_cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simpa only [result] using run

private theorem nip_normal (n q : Nat) (s : ProofStore) (safe : s.cache ≠ 1) :
    Executes (.branch nipCursor) (commandRegisters n q 0 s) .normal
      (searchRegisters ⟨n, q, ⟨s.top, (decode s.stack).2, s.operand, (decode s.stack).1⟩⟩) := by
  have run := literal_nip (commandRegisters n q 0 s) rfl rfl safe
  have result : nipResult (commandRegisters n q 0 s) =
      searchRegisters ⟨n, q, ⟨s.top, (decode s.stack).2, s.operand, (decode s.stack).1⟩⟩ := by
    funext j
    rcases index_cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact Nat.zero_add _
  simpa only [result] using run

private theorem replaced_registers (n q tail mode : Nat) (before after : ProofStore) :
    putRegister (putRegister (putRegister (putRegister
      (putRegister (putRegister (commandRegisters n q mode before) topWff after.top) wffStack after.stack)
      proofList tail) parameterOne after.operand) parameterTwo after.cache) axiomIndex 0 =
      searchRegisters ⟨n, tail, after⟩ := by
  funext j
  rcases index_cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem ax_normal (n q mode : Nat) (s : ProofStore) :
    let y := decode q
    let x := decode y.2
    Executes (.branch axCursor) (commandRegisters n q mode s) .normal
      (searchRegisters ⟨n, x.2, runAxioms mode y.1 x.1 s⟩) := by
  let regs := commandRegisters n q mode s
  have run := literal_axiom regs rfl rfl
  have y : regs proofList = q := rfl
  have ax : regs axiomIndex = mode := by simp [regs, commandRegisters]
  have store : storeOf regs = s := by
    cases s
    rfl
  have result : axiomResult regs =
      searchRegisters ⟨n, (decode (decode q).2).2,
        runAxioms mode (decode q).1 (decode (decode q).2).1 s⟩ := by
    unfold axiomResult
    rw [y, ax, store]
    exact replaced_registers n q _ mode s _
  rw [result] at run
  exact run

theorem command_contracts (foundation berkeley : Nat)
    (extra_normal : ∀ (n q : Nat) (s : ProofStore),
      Executes (.branch extraCursor) (commandRegisters n q 0 s) .normal
        (searchRegisters ⟨n, q, ⟨berkeley, pair foundation (pair s.top s.stack), 0, 0⟩⟩)) :
    CommandsImplemented (runProofCommand foundation berkeley runAxioms) := by
  intro s
  rw [step_decoded]
  let n := nextIndex s
  simp only [unpackCommand]
  generalize hd : decode (payload s) = header
  obtain ⟨selector, rest⟩ := header
  generalize rd : decode rest = arg
  obtain ⟨operand, q⟩ := arg
  let store : ProofStore := {s.store with operand := s.store.operand + operand}
  have entry : beforeDispatch (searchRegisters s) = commandRegisters n q selector store := by
    rw [beforeDispatch_eq, hd]
    dsimp only
    rw [rd]
  have normal {after : SearchState ProofStore}
      (run : Executes (.branch (commandDispatch.select selector).1)
        (commandRegisters n q (commandDispatch.select selector).2 store)
        .normal (searchRegisters after)) :
      Executes mainEdge (searchRegisters s) .normal (searchRegisters after) := by
    apply main_exec rfl rfl (Or.inl rfl)
    rw [entry]
    exact dispatch_to (Or.inl rfl) run
  have halt {after : Registers}
      (run : Executes (.branch (commandDispatch.select selector).1)
        (commandRegisters n q (commandDispatch.select selector).2 store)
        .halt after) :
      Executes mainEdge (searchRegisters s) .halt after := by
    apply main_exec rfl rfl (Or.inr rfl)
    rw [entry]
    exact dispatch_to (Or.inr rfl) run
  rcases selector with _ | _ | _ | _ | mode
  · by_cases eq : store.cache = imp store.top store.operand
    · have run := mp_normal n q store
      simp only [ite_eq_left eq] at run
      have condition : s.store.cache = imp s.store.top (s.store.operand + operand) := eq
      simp only [runProofCommand, ite_eq_left condition, Option.map_some]
      exact normal run
    · have run := mp_normal n q store
      simp only [ite_eq_right eq] at run
      have condition : ¬s.store.cache = imp s.store.top (s.store.operand + operand) := eq
      simp only [runProofCommand, ite_eq_right condition, Option.map_some]
      exact normal run
  · exact normal (drop_normal n q store)
  · by_cases stopped : s.store.cache = 1
    · simp only [runProofCommand, ite_eq_left stopped, Option.map_none]
      obtain ⟨after, ran⟩ := literal_nip_halt (commandRegisters n q 0 store) rfl stopped
      exact ⟨after, halt ran⟩
    · simp only [runProofCommand, ite_eq_right stopped, Option.map_some]
      exact normal (nip_normal n q store stopped)
  · exact normal (extra_normal n q store)
  · exact normal (ax_normal n q mode store)

end I0451.Runtime
