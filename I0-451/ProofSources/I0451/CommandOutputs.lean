module
public import I0451.CommandContracts
public import I0451.Commands.ExtraCommand

/-! The exact literal contradiction search, with the two extracted
EXTRA codes supplied to the command calculus. -/
@[expose] public section
namespace I0451.Runtime

open I0451.Logic M6.Source.Cantor

def proofCommand : CommandEval ProofStore :=
  runProofCommand literalFoundationCode literalBerkeleyCode runAxioms

private theorem extra_field_updates (n q f b : Nat) (s : ProofStore) :
    putRegister (putRegister (putRegister (putRegister
      (putRegister (commandRegisters n q 0 s) topWff b) wffStack (pair f (pair s.top s.stack)))
        parameterOne 0) parameterTwo 0) axiomIndex 0 =
      searchRegisters ⟨n, q, ⟨b, pair f (pair s.top s.stack), 0, 0⟩⟩ := by
  funext j
  rcases index_cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem extra_normal (n q : Nat) (s : ProofStore) :
    Executes (.branch extraCursor) (commandRegisters n q 0 s) .normal
      (searchRegisters ⟨n, q, ⟨literalBerkeleyCode, pair literalFoundationCode (pair s.top s.stack), 0, 0⟩⟩) := by
  have run := literal_extra (commandRegisters n q 0 s) rfl rfl rfl
  have result : extraResult (commandRegisters n q 0 s) =
      searchRegisters ⟨n, q, ⟨literalBerkeleyCode, pair literalFoundationCode (pair s.top s.stack), 0, 0⟩⟩ :=
    extra_field_updates n q literalFoundationCode literalBerkeleyCode s
  rw [result] at run
  exact run

theorem literal_proofCommand : CommandsImplemented proofCommand :=
  command_contracts literalFoundationCode literalBerkeleyCode extra_normal

/-- The exact literal 451-state machine halts exactly when its emitted
theory has a derivation of contradiction in the command calculus. -/
theorem literal_halts_iff_derives :
    Halts literal (blank 0) ↔ Derives literalFoundationCode literalBerkeleyCode 1 :=
  (blank_halts_iff_search literal_proofCommand).trans
    (search_halts_iff_derives_from _ _ boundarySearch
      ⟨Derives.truth, (initial_store_carries Derives.truth).stack, Derives.truth⟩)

end I0451.Runtime
