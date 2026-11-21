module
public import I0451.ArithmeticWordComposition
public import I0451.ArithmeticProofMacros

/-! Fixed proof macros are encoded as internally readable sequences.
The expression lists stay small, and all formula and stack operands
may be arbitrary elements of the arithmetic model. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Logic (Command ProofStore executeCommands executeCommands_append)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem WordRunsTo.empty (s : V) : WordRunsTo ∅ s s := by
  have ran := Iteration.singleton (wordStep ∅) ⟪0, s⟫
  refine ⟨_, by simpa only [lh_empty] using ran, ?_⟩
  simp [ran.begins]

theorem WordRunsTo.single (packet s : V) :
    WordRunsTo (∅ ⁀' packet) s (barePacketStep packet s) := by
  let code := (∅ : V) ⁀' packet
  have seq : Seq (∅ : V) := seq_empty
  have size : lh code = 1 := by simp [code, seq.lh_seqCons]
  have item : znth code 0 = packet := by simpa [code] using znth_append_last seq packet
  have first := Iteration.singleton (wordStep code) ⟪0, s⟫
  have ran := first.append
  change WordRunsTo code s (barePacketStep packet s)
  refine ⟨_, by simpa only [size, zero_add] using ran, ?_⟩
  rw [size, ← zero_add (1 : V), first.append_value, first.begins]
  simp [wordStep, item]

theorem appended_single {left packet : V} (seq : Seq left) :
    AppendedPrefix left (∅ ⁀' packet) (lh (∅ ⁀' packet)) (left ⁀' packet) := by
  have empty : Seq (∅ : V) := seq_empty
  have size : lh ((∅ : V) ⁀' packet) = 1 := by simp [empty.lh_seqCons]
  refine ⟨seq.seqCons _, by rw [size, seq.lh_seqCons], fun i hi => znth_append_old seq _ hi, ?_⟩
  intro i hi
  rw [size] at hi
  have zero : i = 0 := lt_one_iff_eq_zero.mp hi
  subst i
  rw [add_zero, znth_append_last seq]
  simpa using (znth_append_last empty packet).symm

noncomputable def encodeTemplate (word : List (Command V)) : V :=
  word.foldl (fun book cmd => book ⁀' packModelCommand cmd 0) ∅

@[simp] theorem encodeTemplate_nil : encodeTemplate ([] : List (Command V)) = ∅ := rfl

theorem encodeTemplate_snoc (word : List (Command V)) (cmd : Command V) :
    encodeTemplate (word ++ [cmd]) = encodeTemplate word ⁀' packModelCommand cmd 0 := by
  simp [encodeTemplate, List.foldl_append]

theorem encodeTemplate_seq (word : List (Command V)) : Seq (encodeTemplate word) := by
  induction word using List.reverseRecOn with
  | nil => simp
  | append_singleton word cmd ih => rw [encodeTemplate_snoc]; exact ih.seqCons _

theorem encodeTemplate_length (word : List (Command V)) :
    lh (encodeTemplate word) = (word.length : V) := by
  induction word using List.reverseRecOn with
  | nil => simp
  | append_singleton word cmd ih =>
    rw [encodeTemplate_snoc, (encodeTemplate_seq word).lh_seqCons, ih]
    simp [List.length_append, Nat.cast_add]

theorem encodeTemplate_head (cmd : Command V) (rest : List (Command V)) :
    znth (encodeTemplate (cmd :: rest)) 0 = packModelCommand cmd 0 := by
  induction rest using List.reverseRecOn with
  | nil =>
    change znth ((∅ : V) ⁀' packModelCommand cmd 0) 0 = packModelCommand cmd 0
    simpa only [lh_empty] using znth_append_last (seq_empty (V := V)) (packModelCommand cmd 0)
  | append_singleton rest last ih =>
    rw [← List.cons_append, encodeTemplate_snoc]
    have inside : (0 : V) < lh (encodeTemplate (cmd :: rest)) := by
      rw [encodeTemplate_length]
      simp
    rw [znth_append_old (encodeTemplate_seq (cmd :: rest)) _ inside]
    exact ih

theorem barePacketStep_option (cmd : Command V) (s : Option (ProofStore V)) :
    barePacketStep (packModelCommand cmd 0) (encodeStoreResult s) =
      encodeStoreResult (s.bind (runModelCommand cmd)) := by
  cases s with
  | none => simp [encodeStoreResult, barePacketStep]
  | some s => exact barePacketStep_pack cmd s 0

theorem encodeTemplate_runs (word : List (Command V)) (s : Option (ProofStore V)) :
    WordRunsTo (encodeTemplate word) (encodeStoreResult s)
      (encodeStoreResult (s.bind (executeCommands runModelCommand word))) := by
  induction word using List.reverseRecOn with
  | nil =>
    have stays : s.bind (executeCommands runModelCommand []) = s := by cases s <;> rfl
    rw [stays, encodeTemplate_nil]
    exact WordRunsTo.empty _
  | append_singleton word cmd ih =>
    let middle := s.bind (executeCommands runModelCommand word)
    have one := WordRunsTo.single (packModelCommand cmd 0) (encodeStoreResult middle)
    rw [barePacketStep_option] at one
    have joined := ih.append one (appended_single (encodeTemplate_seq word))
    have binds : middle.bind (runModelCommand cmd) =
        s.bind (executeCommands runModelCommand (word ++ [cmd])) := by
      unfold middle
      rw [Option.bind_assoc]
      congr 1
      funext a
      rw [executeCommands_append]
      have single : executeCommands runModelCommand [cmd] = runModelCommand cmd := by
        funext store
        simp only [executeCommands]
        cases runModelCommand cmd store <;> rfl
      rw [single]
    rw [encodeTemplate_snoc]
    simpa only [binds] using joined

theorem ProofEffect.runs {word : List (Command V)} {initial result : ProofStore V}
    (effect : ProofEffect word initial result) :
    WordRunsTo (encodeTemplate word) (packModelStore initial) 0 ∨
      WordRunsTo (encodeTemplate word) (packModelStore initial) (packModelStore result) := by
  have run := encodeTemplate_runs word (some initial)
  simp only [Option.bind_some] at run
  rcases effect with stop | continues
  · rw [stop] at run
    exact .inl run
  · rw [continues] at run
    exact .inr run

end I0451.Arithmetization
