module
public import I0451.ArithmeticBarePackets
public import I0451.ArithmeticCommandReplay

/-! A word of internally many proof commands runs on the literal tape.
The proof synchronizes the proof-store execution with the numeric
tape scheduler, using a backwards pass to encode its pending queues. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime
open I0451.Logic (ProofStore)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def WordRunsTo (word initial result : V) : Prop :=
  ∃ history, Iteration (wordStep word) ⟪0, initial⟫ history (lh word) ∧
    π₂ (znth history (lh word)) = result

noncomputable def withScheduler (next queue store : V) : V :=
  if store = 0 then 0 else packBoundary (modelSearchRegisters next queue (unpackModelStore store))

@[simp] theorem withScheduler_zero (n q : V) : withScheduler n q 0 = 0 := by simp [withScheduler]

theorem withScheduler_pack (n q : V) (s : ProofStore V) :
    withScheduler n q (packModelStore s) = packBoundary (modelSearchRegisters n q s) := by
  simp only [withScheduler, ite_eq_right (packModelStore_nonzero s), unpack_packModelStore]

private theorem withScheduler_defined {k : Nat} (next queue store : (Fin k → V) → V)
    (dn : 𝚺ᴬ₁.DefinableFunction (V := V) next) (dq : 𝚺ᴬ₁.DefinableFunction (V := V) queue)
    (ds : 𝚺ᴬ₁.DefinableFunction (V := V) store) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => withScheduler (next v) (queue v) (store v)) := by
  have zero : 𝚺ᴬ₁.DefinableFunction (V := V) (fun _ : Fin k → V => (0 : V)) :=
    Bounding.HierarchySymbol.DefinableFunction.const 0
  exact arithmeticCompare_defined store _ _ _ ds zero zero
    (packBoundary_definable _ (searchRegisters_modelDefined next queue store dn dq ds))

private theorem lift_store_result (n q : V) (result : Option (ProofStore V)) :
    withScheduler n q (encodeStoreResult result) = codeOfResult (result.map (modelSearchRegisters n q)) := by
  cases result
  · exact withScheduler_zero n q
  · exact withScheduler_pack n q _

private theorem scheduler_bare_queued (n tail packet store : V) :
    boundaryCodeStep (withScheduler n (packetWithTail packet tail + 1) store) =
      withScheduler n tail (barePacketStep packet store) := by
  by_cases empty : store = 0
  · subst store
    simp [barePacketStep, boundaryCodeStep]
  obtain ⟨cmd, original, rfl⟩ := packModelCommand_surjective packet
  rw [barePacketStep_command _ _ _ empty, packetWithTail_packModelCommand, lift_store_result]
  simp only [withScheduler, ite_eq_right empty, boundaryCodeStep_pack (modelSearchRegisters_ready _ _ _)]
  rw [modelCommandStep_queued]

private theorem scheduler_bare_fresh (tail packet store : V) :
    boundaryCodeStep (withScheduler (packetWithTail packet tail) 0 store) =
      withScheduler (packetWithTail packet tail + 1) tail (barePacketStep packet store) := by
  by_cases empty : store = 0
  · subst store
    simp [barePacketStep, boundaryCodeStep]
  obtain ⟨cmd, original, rfl⟩ := packModelCommand_surjective packet
  rw [barePacketStep_command _ _ _ empty, packetWithTail_packModelCommand, lift_store_result]
  simp only [withScheduler, ite_eq_right empty, boundaryCodeStep_pack (modelSearchRegisters_ready _ _ _)]
  rw [modelCommandStep_fresh]

private theorem sync_word {word writer simulated physical candidate : V} {s : ProofStore V}
    (written : Iteration (queueWriter word) ⟪0, 0⟫ writer (lh word))
    (ran : Iteration (wordStep word) ⟪0, packModelStore s⟫ simulated (lh word))
    (tape : Iteration boundaryCodeStep (packBoundary (modelSearchRegisters candidate 0 s)) physical (lh word))
    (candidateCode : candidate = encodedQueueAt word writer 0 - 1) :
    ∀ i ≤ lh word, znth physical i = withScheduler
      (if i = 0 then candidate else candidate + 1)
      (if i = 0 then 0 else encodedQueueAt word writer i) (π₂ (znth simulated i)) := by
  let next (i : V) := if i = 0 then candidate else candidate + 1
  let queue (i : V) := if i = 0 then 0 else encodedQueueAt word writer i
  change ∀ i ≤ lh word, znth physical i =
    withScheduler (next i) (queue i) (π₂ (znth simulated i))
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | zero =>
    intro _
    rw [tape.begins, ran.begins]
    simp [next, queue, withScheduler_pack]
  | succ i ih =>
    intro within
    have before := succ_le_iff_lt.mp within
    have active := ih (le_of_lt before)
    have commanded := ran.advances i before
    have atIndex := wordStep_index ran i (le_of_lt before)
    have store : π₂ (znth simulated (i + 1)) =
        barePacketStep (znth word i) (π₂ (znth simulated i)) := by
      simp only [commanded, wordStep, pi₂_pair, atIndex]
    have code := encodedQueueAt_cons written before
    have positive : i + 1 ≠ 0 := by simp
    rw [tape.advances i before, active, store]
    simp only [next, queue, ite_eq_right positive]
    by_cases isFirst : i = 0
    · subst i
      simp only [ite_true] at code ⊢
      have payload : candidate = packetWithTail (znth word 0) (encodedQueueAt word writer (0 + 1)) := by
        rw [candidateCode, code, add_tsub_cancel_right]
      rw [payload]
      exact scheduler_bare_fresh _ _ _
    · simp only [ite_eq_right isFirst, code]
      exact scheduler_bare_queued _ _ _ _
  | hP =>
    have nextDefined : 𝚺ᴬ₁-Function₁[V] next :=
      arithmeticCompare_defined (fun v : Fin 1 → V => v 0) (fun _ => 0)
        (fun _ => candidate) (fun _ => candidate + 1)
        (by definability) (by definability) (by definability) (by definability)
    have queueDefined : 𝚺ᴬ₁-Function₁[V] queue :=
      arithmeticCompare_defined (fun v : Fin 1 → V => v 0) (fun _ => 0)
        (fun _ => 0) (fun v => encodedQueueAt word writer (v 0))
        (by definability) (by definability) (by definability) (encodedQueueAt_definable word writer)
    have liftDefined : 𝚺ᴬ₁-Function₁[V] (fun i => withScheduler (next i) (queue i) (π₂ (znth simulated i))) :=
      withScheduler_defined (fun v : Fin 1 → V => next (v 0)) (fun v => queue (v 0))
        (fun v => π₂ (znth simulated (v 0))) nextDefined queueDefined (by definability)
    definability

/-- Any internally finite word that halts from every incoming proof
store gives a blank-tape halt when its candidate is reached. -/
theorem literal_halts_of_internal_word {word writer : V}
    (written : Iteration (queueWriter word) ⟪0, 0⟫ writer (lh word))
    (later : (3 : V) ≤ encodedQueueAt word writer 0 - 1)
    (stops : ∀ s : ProofStore V, WordRunsTo word (packModelStore s) 0) :
    (haltsDef literal).val.Evalb (![] : Fin 0 → V) := by
  let candidate := encodedQueueAt word writer 0 - 1
  apply literal_halts_of_coded_candidate candidate later
  intro regs ready index empty
  let store := readModelStore regs
  have before := ready.boundaryRegisters
  rw [index, empty] at before
  have same : modelSearchRegisters candidate 0 store = regs := before
  rw [← same]
  obtain ⟨executed, ran, stopped⟩ := stops store
  obtain ⟨physical, tape⟩ := coded_command_history_exists
    (packBoundary (modelSearchRegisters candidate 0 store)) (lh word)
  have synced := sync_word written ran tape (show candidate = _ from rfl) (lh word) (le_refl _)
  rw [stopped, withScheduler_zero] at synced
  obtain ⟨last, valid⟩ := tape.command_run_of_zero (packBoundary_nonzero _) synced
  exact ⟨physical, last, valid⟩

end I0451.Arithmetization
