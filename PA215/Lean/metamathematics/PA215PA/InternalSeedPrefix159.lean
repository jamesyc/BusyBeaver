import PA215PA.InternalCodedSourceNatTrace
import PA215PA.InternalCodedSourceTraceDeterminism
import PA215PA.InternalStartupHaltingBridge
namespace PA215.PA.InternalTrace.FixedTrace
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CodedSource

def seedRegisters : List Nat := [0,1,1,0,0,0,0,0,0]
noncomputable def seedState {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] : V :=
  stateCode 26 (fixedFile seedRegisters)
def seedGraph : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “c. ∃ regs, !(fixedFileGraph seedRegisters) regs ∧ !adjoinDef c 26 regs”
def seedPrefixSentence : ArithmeticSentence :=
  “∃ a b cs, !seedGraph a ∧ !entryGraph b ∧ !traceGraph 159 cs a b”

lemma seed_correct {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] (v : Fin 1 → V) :
    (V ⊧/v seedGraph.val) ↔ v 0=seedState := by
  simp [seedGraph,fixedFile_correct,adjoin_defined.df,seedState,stateCode,numeral_eq_natCast,Nat.cast_ofNat]

lemma encode_seed : encodeSource Source.SeedPrefix.seed=seedState (V := Nat) := by
  have h : List.ofFn Source.SeedPrefix.seed.registers=seedRegisters := by decide
  change stateCode 26 (fixedFile (List.ofFn Source.SeedPrefix.seed.registers))=
    stateCode 26 (fixedFile seedRegisters)
  rw [h]
  rfl
lemma encode_intermediate : encodeSource Source.SeedPrefix.intermediate=entryState (V := Nat) := by
  have h : List.ofFn Source.SeedPrefix.intermediate.registers=startupRegisters := by decide
  change stateCode 69 (fixedFile (List.ofFn Source.SeedPrefix.intermediate.registers))=
    stateCode 69 (fixedFile startupRegisters)
  rw [h]
  rfl

lemma seed_prefix_nat : ∃ cs : Nat, Trace 159 cs seedState entryState := by
  have h := cycles_to_trace Source.SeedPrefix.cyclic_trace
    (show SourceValid Source.SeedPrefix.seed from ⟨by decide,by decide⟩)
  simpa only [encode_seed,encode_intermediate] using h

lemma seedPrefix_sigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 seedPrefixSentence := by
  simp [seedPrefixSentence]

theorem pa_proves_seed_prefix : theory ⊢ seedPrefixSentence := by
  apply Arithmetic.sigma_one_completeness seedPrefix_sigma
  simpa [seedPrefixSentence,models_iff,seed_correct,entry_correct,trace_correct,
    numeral_eq_natCast,natCast_nat] using seed_prefix_nat

theorem seed_prefix_all_models {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] :
    ∃ cs : V, Trace 159 cs seedState entryState := by
  have h := consequence_iff.mp (Theory.Proof.sound pa_proves_seed_prefix) V inferInstance
  simpa [seedPrefixSentence,models_iff,seed_correct,entry_correct,trace_correct,
    numeral_eq_natCast,Nat.cast_ofNat] using h

/-- Derived from deterministic arbitrary-model traces and absorbing halt;
there is no hidden premise excluding halt during the fixed159-step prefix. -/
theorem seed_halts_iff_intermediate {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] :
    (∃ n cs b : V, Trace n cs seedState b ∧ control b=0) ↔
    (∃ n cs b : V, Trace n cs entryState b ∧ control b=0) := by
  obtain ⟨ps,hp⟩ := seed_prefix_all_models (V := V)
  exact prefix_halting_iff hp

theorem seed_no_early_halt {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
    {n cs b : V} (h : Trace n cs seedState b) (hn : n≤159) (hb : control b=0) : False := by
  obtain ⟨ps,hp⟩ := seed_prefix_all_models (V := V)
  have hm : control (entryState (V := V))≠0 := by simp [entryState]
  exact prefix_excludes_early_halt hp hm h hn hb

#print axioms seed_prefix_nat
#print axioms pa_proves_seed_prefix
#print axioms seed_prefix_all_models
#print axioms seed_halts_iff_intermediate
#print axioms seed_no_early_halt
end PA215.PA.InternalTrace.FixedTrace
