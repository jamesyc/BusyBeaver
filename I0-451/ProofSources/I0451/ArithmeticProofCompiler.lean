module
public import I0451.ArithmeticWordTemplates

/-! Compose proof words with a single-formula stack contract. Each
primitive template has bounded length; concatenation and execution
work on sequence codes of arbitrary model-valued length. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime
open I0451.Logic (Command ProofStore executeCommands)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def EncodedEffect (word : V) (first last : ProofStore V) : Prop :=
  WordRunsTo word (packModelStore first) 0 ∨ WordRunsTo word (packModelStore first) (packModelStore last)

theorem EncodedEffect.append {a b full : V} {first mid last : ProofStore V}
    (before : EncodedEffect a first mid) (after : EncodedEffect b mid last)
    (joined : AppendedPrefix a b (lh b) full) : EncodedEffect full first last := by
  rcases before with stop | moved
  · exact .inl (stop.append (WordRunsTo.zero b) joined)
  · rcases after with stop | done
    · exact .inl (moved.append stop joined)
    · exact .inr (moved.append done joined)

theorem ProofEffect.encoded {word : List (Command V)} {first last : ProofStore V}
    (effect : ProofEffect word first last) : EncodedEffect (encodeTemplate word) first last :=
  effect.runs

/-- A command word either halts or pushes the formula over any incoming
stack, with all other proof-store registers returned to zero. -/
def CompiledPushes (formula : V) : Prop :=
  ∃ word, Seq word ∧ ∀ tail,
    EncodedEffect word (neutralStore tail) (neutralStore (cantor formula tail))

theorem CompiledPushes.template {form : V} (word : List (Command V))
    (runs : ∀ tail, ProofEffect word (neutralStore tail) (neutralStore (cantor form tail))) :
    CompiledPushes form :=
  ⟨encodeTemplate word, encodeTemplate_seq word, fun tail => (runs tail).encoded⟩

theorem compiled_truth : CompiledPushes (0 : V) :=
  CompiledPushes.template (saveModelTop 0) fun tail => save_model_top_effect 0 tail 0 0

theorem compiled_foundation : CompiledPushes (literalFoundationCode : V) :=
  CompiledPushes.template _ push_model_foundation

theorem compiled_berkeley : CompiledPushes (literalBerkeleyCode : V) :=
  CompiledPushes.template _ push_model_berkeley

theorem compiled_bundle {a b c : V} (firstFresh : c ≠ a) (secondFresh : c ≠ b) :
    CompiledPushes (modelEncoding.bundle a b c) :=
  CompiledPushes.template _ (push_model_bundle firstFresh secondFresh)

theorem compiled_head {a b c x f : V} (head : f ∈ modelEncoding.heads a b c x) :
    CompiledPushes f := by
  obtain ⟨word, effect⟩ := push_model_head head
  exact CompiledPushes.template word effect

theorem CompiledPushes.generalize {f : V} (given : CompiledPushes f) (label : V) :
    CompiledPushes (modelEncoding.all label f) := by
  obtain ⟨word, seq, run⟩ := given
  obtain ⟨program, joined⟩ := appendedSequence_exists seq (encodeTemplate (generalizeModelWord label))
  exact ⟨program, joined.sequence, fun tail =>
    (run tail).append (generalize_model_effect label f tail).encoded joined⟩

theorem CompiledPushes.detach {a b : V} (antecedent : CompiledPushes a)
    (conditional : CompiledPushes (modelImp a b)) : CompiledPushes b := by
  obtain ⟨p, _, proveA⟩ := antecedent
  obtain ⟨q, hq, proveImp⟩ := conditional
  obtain ⟨premises, joined⟩ := appendedSequence_exists hq p
  obtain ⟨proof, final⟩ := appendedSequence_exists joined.sequence (encodeTemplate (detachModelWord b))
  refine ⟨proof, final.sequence, fun tail => ?_⟩
  have loaded := (proveImp tail).append (proveA (cantor (modelImp a b) tail)) joined
  exact loaded.append (detach_model_effect a b tail).encoded final

private def startProofWord : List (Command V) := .extra 0 :: saveModelTop 0

private noncomputable def initialStack (s : ProofStore V) : V :=
  cantor (literalBerkeleyCode : V) (cantor (literalFoundationCode : V) (cantor s.top s.stack))

private theorem start_proof_run (s : ProofStore V) :
    EncodedEffect (encodeTemplate (startProofWord (V := V))) s (neutralStore (initialStack s)) := by
  let stack := cantor (literalFoundationCode : V) (cantor s.top s.stack)
  have header : ProofEffect [.extra 0] s ⟨(literalBerkeleyCode : V), stack, 0, 0⟩ :=
    ProofEffect.singleton rfl
  exact (header.append (save_model_top_effect _ stack 0 0)).encoded

private theorem contradiction_trailer (tail : V) :
    WordRunsTo (encodeTemplate ([.nip 0, .nip 0] : List (Command V)))
      (packModelStore (neutralStore (cantor 1 tail))) 0 := by
  have ran : executeCommands runModelCommand [.nip 0, .nip 0] (neutralStore (cantor 1 tail)) = none := by
    simp [executeCommands, runModelCommand, neutralStore]
  have execution := encodeTemplate_runs [.nip 0, .nip 0] (some (neutralStore (cantor 1 tail)))
  simp only [Option.bind_some, ran] at execution
  exact execution

private theorem candidate_extra_bound (tail : V) : (3 : V) ≤ packModelCommand (.extra 0) tail := by
  have small : (2 : V) + 0 < 3 + cantor (0 : V) tail := by
    have lt : (2 : V) < 3 := (Nat.cast_lt (α := V)).mpr (by decide : (2 : Nat) < 3)
    simpa only [add_zero] using lt_of_lt_of_le lt (show (3 : V) ≤ 3 + cantor (0 : V) tail by simp)
  have bound := cantor_diagonal_lt (2 : V) 0 3 (cantor 0 tail) small
  have three : cantor (2 : V) 0 = 3 := by
    simpa only [show M6.Source.Cantor.pair 2 0 = 3 from rfl, Nat.cast_ofNat, Nat.cast_zero] using
      (cantor_cast (V := V) 2 0).symm
  exact le_of_lt (three ▸ bound)

theorem literal_halts_of_compiled_contradiction (proof : CompiledPushes (1 : V)) :
    (haltsDef literal).val.Evalb (![] : Fin 0 → V) := by
  obtain ⟨word, _, compiled⟩ := proof
  let boot := encodeTemplate (startProofWord (V := V))
  let trailer := encodeTemplate ([.nip 0, .nip 0] : List (Command V))
  have startSeq : Seq boot := encodeTemplate_seq _
  obtain ⟨prefixCode, prefixAssembly⟩ := appendedSequence_exists startSeq word
  obtain ⟨code, assembly⟩ := appendedSequence_exists prefixAssembly.sequence trailer
  obtain ⟨writer, written⟩ := queueWriter_exists code 0
  have bootNonempty : (0 : V) < lh boot := by
    change (0 : V) < lh (encodeTemplate (startProofWord (V := V)))
    rw [encodeTemplate_length]
    simp [startProofWord]
  have prefixNonempty : (0 : V) < lh prefixCode := by
    rw [prefixAssembly.length]
    exact lt_of_lt_of_le bootNonempty (by simp)
  have nonempty : (0 : V) < lh code := by
    rw [assembly.length]
    exact lt_of_lt_of_le prefixNonempty (by simp)
  have starts : znth code 0 = packModelCommand (.extra 0) 0 := by
    rw [assembly.first 0 prefixNonempty, prefixAssembly.first 0 bootNonempty]
    exact encodeTemplate_head (.extra 0) _
  have startQueue := encodedQueueAt_cons written nonempty
  rw [starts, packetWithTail_packModelCommand] at startQueue
  have later : (3 : V) ≤ encodedQueueAt code writer 0 - 1 := by
    rw [startQueue, add_tsub_cancel_right]
    exact candidate_extra_bound _
  apply literal_halts_of_internal_word written later
  intro store
  have normal := (start_proof_run store).append (compiled (initialStack store)) prefixAssembly
  rcases normal with stopped | concluded
  · exact stopped.append (WordRunsTo.zero trailer) assembly
  · exact concluded.append (contradiction_trailer (initialStack store)) assembly

end I0451.Arithmetization
