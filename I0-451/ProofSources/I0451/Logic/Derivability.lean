module
public import I0451.Logic.SearchMacros

/-! The numeric Hilbert calculus searched by the proof-store commands.
Its contradiction is the literal code one. -/
@[expose] public section
namespace I0451.Logic

open M6.Source.Cantor

inductive Derives (foundation berkeley : Nat) : Nat → Prop where
  | truth : Derives foundation berkeley 0
  | foundation : Derives foundation berkeley foundation
  | berkeley : Derives foundation berkeley berkeley
  | head (a b c x f : Nat) (member : f ∈ heads a b c x) :
      Derives foundation berkeley f
  | bundle (a b c : Nat) (left : c ≠ a) (right : c ≠ b) :
      Derives foundation berkeley (Logic.bundle a b c)
  | gen (label f : Nat) (derived : Derives foundation berkeley f) :
      Derives foundation berkeley (all label f)
  | mp {a b : Nat} (antecedent : Derives foundation berkeley a)
      (implication : Derives foundation berkeley (imp a b)) :
      Derives foundation berkeley b

theorem Derives.sound {V : Type} {E : V → V → Prop} (M : BundleModel E)
    {foundation berkeley f : Nat} (found : Valid E foundation) (large : Valid E berkeley)
    (proof : Derives foundation berkeley f) : Valid E f := by
  induction proof with
  | truth => exact valid_zero E
  | foundation => exact found
  | berkeley => exact large
  | head a b c x f member => exact heads_valid M.irrefl a b c x f member
  | bundle a b c l r => exact bundle_valid M (Ne.symm l) (Ne.symm r)
  | gen label f derives ih =>
    intro values
    rw [eval_all]
    exact fun v => ih (assign values label v)
  | mp a b ihA ihB => exact fun values => (eval_imp E values _ _).mp (ihB values) (ihA values)

private theorem axioms_derive {foundation berkeley : Nat} (mode y formula : Nat)
    (s : ProofStore) (given : s.Carries (Derives foundation berkeley)) :
    (runAxioms mode y formula s).Carries (Derives foundation berkeley) := by
  let D := Derives foundation berkeley
  have saved := (codeStack_pair D s.top s.stack).2 ⟨given.top, given.stack⟩
  have generalized := Derives.gen s.operand s.cache given.cache
  have base := (codeStack_pair D (all s.operand s.cache) _).2 ⟨generalized, saved⟩
  constructor
  · change D (if mode = s.operand ∨ mode = s.cache + y then 0 else bundle s.operand (s.cache + y) mode)
    split
    · exact .truth
    · rename_i guard
      exact .bundle _ _ _ (fun e => guard (Or.inl e)) (fun e => guard (Or.inr e))
  · exact CodeStack.foldr _ (fun f member => Derives.head _ _ _ _ f member) base
  · exact .truth

theorem Derives.compile {foundation berkeley f : Nat} (proof : Derives foundation berkeley f) :
    Pushes foundation berkeley f := by
  induction proof with
  | truth => exact pushes_truth _ _
  | foundation => exact pushes_extra_foundation _ _
  | berkeley => exact pushes_extra_berkeley _ _
  | head a b c x f member => exact pushes_head _ _ a b c x f member
  | bundle a b c left right => exact pushes_bundle _ _ left right
  | gen label f derives ih => exact pushes_generalize ih label
  | mp a b ihA ihB => exact pushes_mp ihA ihB

def initialSearch : SearchState ProofStore := ⟨0, 0, neutral 0⟩

theorem word_halts_of_contradiction {foundation berkeley : Nat}
    (contradiction : Derives foundation berkeley 1) :
    ∃ rest, ∀ store, executeCommands (runProofCommand foundation berkeley runAxioms)
      (.extra 0 :: rest) store = none := by
  obtain ⟨word, extras, works⟩ := contradiction.compile
  refine ⟨[.ax 0 0 0 0] ++ word ++ [.nip 0, .nip 0], fun store => ?_⟩
  let exec := runProofCommand foundation berkeley runAxioms
  let afterExtra : ProofStore := ⟨berkeley, pair foundation (pair store.top store.stack), 0, 0⟩
  let afterAxioms := runAxioms 0 0 0 afterExtra
  have flow := works afterAxioms.stack
  change executeCommands exec word (neutral afterAxioms.stack) = none ∨
    executeCommands exec word (neutral afterAxioms.stack) =
      some (neutral (pushList (1 :: extras) afterAxioms.stack)) at flow
  simp only [List.singleton_append, executeCommands]
  change executeCommands exec (word ++ [.nip 0, .nip 0]) (neutral afterAxioms.stack) = none
  rw [executeCommands_append]
  rcases flow with stopped | ran
  · rw [stopped]
    rfl
  · rw [ran]
    let tail := pushList extras afterAxioms.stack
    have read : exec (.nip 0) (neutral (pair 1 tail)) = some ⟨0, tail, 0, 1⟩ := by
      simp [exec, runProofCommand, neutral, decode_pair]
    have halt : exec (.nip 0) ⟨0, tail, 0, 1⟩ = none := rfl
    change executeCommands exec [.nip 0, .nip 0] (neutral (pair 1 tail)) = none
    simp only [executeCommands, read, Option.bind_some, halt, Option.bind_none]

/-- Exact abstract search result from any normalized store carrying
theorems. The ignored EXTRA operand permits every starting candidate. -/
theorem search_halts_iff_derives_from (foundation berkeley : Nat) (start : SearchState ProofStore)
    (valid : start.store.Carries (Derives foundation berkeley)) :
    SearchHalts (runProofCommand foundation berkeley runAxioms) start ↔
      Derives foundation berkeley 1 := by
  constructor
  · intro halted
    apply Classical.byContradiction
    intro noContradiction
    exact search_closed Derives.truth (fun _ _ => Derives.mp) noContradiction
      Derives.foundation Derives.berkeley axioms_derive valid halted
  · intro proof
    obtain ⟨rest, runs⟩ := word_halts_of_contradiction proof
    have bound : start.nextCandidate ≤ packCandidate (.extra start.nextCandidate :: rest) := by
      simp only [packCandidate, packCommand]
      have inner := pair_ge start.nextCandidate (packQueued rest)
      have outer := pair_ge 3 (pair start.nextCandidate (packQueued rest))
      omega
    exact halts_of_command_word (.extra start.nextCandidate) rest bound runs

theorem search_halts_iff_derives (foundation berkeley : Nat) :
    SearchHalts (runProofCommand foundation berkeley runAxioms) initialSearch ↔
      Derives foundation berkeley 1 :=
  search_halts_iff_derives_from foundation berkeley initialSearch (initial_store_carries Derives.truth)

end I0451.Logic
