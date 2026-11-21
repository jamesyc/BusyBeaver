module
public import I0451.Logic.Scheduler

/-! Proof-store operations for MP, DROP, NIP, and EXTRA. The separate
axiom-bundle routine supplies the AX operation. Its preservation contract
is explicit in this module and must be discharged by the compiler proof. -/
@[expose] public section
namespace I0451.Logic

open M6.Source.Cantor

structure ProofStore (α : Type := Nat) where
  top : α
  stack : α
  operand : α
  cache : α
  deriving DecidableEq, Repr

def stackAt : Nat → Nat → Nat
  | 0, stack => (decode stack).1
  | k + 1, stack => stackAt k (decode stack).2

def Valid {V : Type} (E : V → V → Prop) (code : Nat) : Prop :=
  ∀ values : Nat → V, Eval E values code

def CodeStack (P : Nat → Prop) (stack : Nat) : Prop :=
  ∀ position, P (stackAt position stack)

theorem codeStack_pair (P : Nat → Prop) (head tail : Nat) :
    CodeStack P (pair head tail) ↔ P head ∧ CodeStack P tail := by
  constructor
  · intro contents
    refine ⟨?_, fun n => ?_⟩
    · simpa only [stackAt, decode_pair] using contents 0
    · simpa only [stackAt, decode_pair] using contents (n + 1)
  · rintro ⟨first, rest⟩ position
    cases position with
    | zero => simpa only [stackAt, decode_pair] using first
    | succ n => simpa only [stackAt, decode_pair] using rest n

theorem CodeStack.pop {P : Nat → Prop} {stack : Nat} (contents : CodeStack P stack) :
    P (decode stack).1 ∧ CodeStack P (decode stack).2 :=
  ⟨contents 0, fun n => contents (n + 1)⟩

theorem CodeStack.foldr {P : Nat → Prop} (forms : List Nat) {tail : Nat}
    (valid : ∀ f ∈ forms, P f) (rest : CodeStack P tail) :
    CodeStack P (forms.foldr pair tail) := by
  induction forms with
  | nil => exact rest
  | cons first remaining ih =>
    apply (codeStack_pair P first _).2
    exact ⟨valid first (by simp), ih (fun f hf => valid f (List.mem_cons_of_mem _ hf))⟩

abbrev ValidStack {V : Type} (E : V → V → Prop) := CodeStack (Valid E)

theorem validStack_pair {V : Type} {E : V → V → Prop} (head tail : Nat) :
    ValidStack E (pair head tail) ↔ Valid E head ∧ ValidStack E tail :=
  codeStack_pair (Valid E) head tail

structure ProofStore.Carries (P : Nat → Prop) (s : ProofStore) : Prop where
  top : P s.top
  stack : CodeStack P s.stack
  cache : P s.cache

abbrev ProofStore.Invariant {V : Type} (E : V → V → Prop) := ProofStore.Carries (Valid E)

abbrev AxiomRoutine := Nat → Nat → Nat → ProofStore → ProofStore

/-- Run one command, after incorporating its numeric operand. AX is the
only case delegated to the formula-bundle routine. -/
def runProofCommand (foundation berkeley : Nat) (ax : AxiomRoutine) :
    CommandEval ProofStore
  | .mp p, s =>
    let arg := s.operand + p
    if s.cache = imp s.top arg then some ⟨arg, pair 0 s.stack, arg, 0⟩
    else some ⟨0, s.stack, arg, 0⟩
  | .drop p, s =>
    some ⟨s.cache, pair s.top s.stack, s.operand + p, s.cache⟩
  | .nip p, s =>
    if s.cache = 1 then none
    else some ⟨s.top, (decode s.stack).2, s.operand + p, (decode s.stack).1⟩
  | .extra _, s =>
    some ⟨berkeley, pair foundation (pair s.top s.stack), 0, 0⟩
  | .ax mode p y formula, s =>
    some (ax mode y formula { s with operand := s.operand + p })

theorem valid_zero {V : Type} (E : V → V → Prop) : Valid E 0 := fun s => eval_zero E s

theorem initial_store_carries {P : Nat → Prop} (zeroProof : P 0) :
    ProofStore.Carries P ⟨0, 0, 0, 0⟩ := by
  refine ⟨zeroProof, ?_, zeroProof⟩
  intro n
  have zero : stackAt n 0 = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  rw [zero]
  exact zeroProof

theorem initial_store_valid {V : Type} (E : V → V → Prop) :
    ProofStore.Invariant E ⟨0, 0, 0, 0⟩ :=
  initial_store_carries (valid_zero E)

theorem runProofCommand_closed {P : Nat → Prop} {foundation berkeley : Nat} {ax : AxiomRoutine}
    (truth : P 0) (detachment : ∀ a b, P a → P (imp a b) → P b)
    (noContradiction : ¬ P 1) (foundationValid : P foundation) (berkeleyValid : P berkeley)
    (axiomsValid : ∀ mode y formula s, s.Carries P → (ax mode y formula s).Carries P)
    (command : Command) {s : ProofStore} (invariant : s.Carries P) :
    ∃ t, runProofCommand foundation berkeley ax command s = some t ∧ t.Carries P := by
  cases command with
  | mp p =>
    by_cases succeeds : s.cache = imp s.top (s.operand + p)
    · have consequence : P (s.operand + p) :=
        detachment _ _ invariant.top (succeeds ▸ invariant.cache)
      refine ⟨⟨s.operand + p, pair 0 s.stack, s.operand + p, 0⟩, ?_, ⟨consequence, (codeStack_pair P 0 s.stack).2 ⟨truth, invariant.stack⟩,
        truth⟩⟩
      simp [runProofCommand, succeeds]
    · refine ⟨⟨0, s.stack, s.operand + p, 0⟩, ?_, ⟨truth, invariant.stack, truth⟩⟩
      simp [runProofCommand, succeeds]
  | drop p =>
    exact ⟨_, rfl, ⟨invariant.cache, (codeStack_pair P s.top s.stack).2 ⟨invariant.top, invariant.stack⟩,
      invariant.cache⟩⟩
  | nip p =>
    have nonterminal : s.cache ≠ 1 := fun eq => noContradiction (eq ▸ invariant.cache)
    obtain ⟨topOfStack, remaining⟩ := invariant.stack.pop
    exact ⟨⟨s.top, _, s.operand + p, _⟩, by simp [runProofCommand, nonterminal],
      ⟨invariant.top, remaining, topOfStack⟩⟩
  | extra p =>
    have saved := (codeStack_pair P s.top s.stack).2 ⟨invariant.top, invariant.stack⟩
    exact ⟨_, rfl, ⟨berkeleyValid, (codeStack_pair P foundation _).2 ⟨foundationValid, saved⟩,
      truth⟩⟩
  | ax mode p y formula =>
    exact ⟨_, rfl, axiomsValid mode y formula _ ⟨invariant.top, invariant.stack, invariant.cache⟩⟩

/-- A proof predicate closed under the command operations excludes
a search halt if it excludes the contradiction code. -/
theorem search_closed {P : Nat → Prop} {foundation berkeley : Nat} {ax : AxiomRoutine}
    (truth : P 0) (detachment : ∀ a b, P a → P (imp a b) → P b)
    (noContradiction : ¬ P 1) (foundationValid : P foundation) (berkeleyValid : P berkeley)
    (axiomsValid : ∀ mode y formula s, s.Carries P → (ax mode y formula s).Carries P)
    {s : SearchState ProofStore} (invariant : s.store.Carries P) :
    ¬ SearchHalts (runProofCommand foundation berkeley ax) s := by
  let execute := runProofCommand foundation berkeley ax
  have progress (s : SearchState ProofStore) (h : s.store.Carries P) :
      ∃ t, s.step execute = some t ∧ t.store.Carries P := by
    let load := s.queued == 0
    let payload := if load then s.nextCandidate else s.queued - 1
    obtain ⟨store, ran, good⟩ := runProofCommand_closed truth detachment noContradiction foundationValid berkeleyValid
      axiomsValid (unpackCommand payload).1 h
    refine ⟨⟨if load then s.nextCandidate + 1 else s.nextCandidate, (unpackCommand payload).2, store⟩,
      ?_, good⟩
    exact congrArg (Option.map fun after => (⟨if load then s.nextCandidate + 1 else s.nextCandidate,
      (unpackCommand payload).2, after⟩ : SearchState ProofStore)) ran
  rintro ⟨fuel, stop⟩
  induction fuel generalizing s with
  | zero => simp [SearchState.run] at stop
  | succ fuel ih =>
    obtain ⟨t, move, good⟩ := progress s invariant
    rw [SearchState.run, move] at stop
    exact ih good stop

/-- The command search cannot reach the contradiction test in an
irreflexive model satisfying the emitted axioms and axiom-bundle clauses. -/
theorem search_model_sound {V : Type} {E : V → V → Prop} (point : V)
    (irrefl : ∀ x, ¬ E x x) {foundation berkeley : Nat} {ax : AxiomRoutine}
    (foundationValid : Valid E foundation) (berkeleyValid : Valid E berkeley)
    (axiomsValid : ∀ mode y formula s, s.Invariant E → (ax mode y formula s).Invariant E)
    {s : SearchState ProofStore} (invariant : s.store.Invariant E) :
    ¬ SearchHalts (runProofCommand foundation berkeley ax) s :=
  search_closed (valid_zero E)
    (fun a b antecedent implication values =>
      (eval_imp E values a b).1 (implication values) (antecedent values))
    (fun proof => eval_false (fun _ => point) irrefl (proof (fun _ => point)))
    foundationValid berkeleyValid axiomsValid invariant

end I0451.Logic
