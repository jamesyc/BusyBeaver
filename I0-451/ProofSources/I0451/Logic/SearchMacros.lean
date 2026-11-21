module
public import I0451.Logic.AxiomBundle

/-! Composable proof words. A word may halt early when a popped proof is
already the contradiction. Otherwise it has the stated stack effect. -/
@[expose] public section
namespace I0451.Logic

open M6.Source.Cantor

def pushList (forms : List Nat) (tail : Nat) : Nat := forms.foldr pair tail

@[simp] theorem pushList_nil (tail : Nat) : pushList [] tail = tail := rfl
@[simp] theorem pushList_cons (head : Nat) (forms : List Nat) (tail : Nat) :
    pushList (head :: forms) tail = pair head (pushList forms tail) := rfl

theorem pushList_append (xs ys : List Nat) (tail : Nat) :
    pushList (xs ++ ys) tail = pushList xs (pushList ys tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

def neutral (stack : Nat) : ProofStore := ⟨0, stack, 0, 0⟩

/-- Either the search stops during the word or it finishes at the stated store. -/
def Effect (foundation berkeley : Nat) (word : List Command) (first last : ProofStore) : Prop :=
  let run := executeCommands (runProofCommand foundation berkeley runAxioms) word first
  run = none ∨ run = some last

theorem executeCommands_append {α Store : Type} (exec : Command α → Store → Option Store)
    (first rest : List (Command α)) (start : Store) :
    executeCommands exec (first ++ rest) start =
      (executeCommands exec first start).bind (executeCommands exec rest) := by
  induction first generalizing start with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, executeCommands]
    cases exec c start
    · rfl
    · next mid => exact ih mid

theorem Effect.then {foundation berkeley : Nat} {first rest : List Command} {s t u : ProofStore}
    (a : Effect foundation berkeley first s t) (b : Effect foundation berkeley rest t u) :
    Effect foundation berkeley (first ++ rest) s u := by
  unfold Effect at a b ⊢
  dsimp only at a b ⊢
  rw [executeCommands_append]
  rcases a with a | a
  · exact Or.inl (by rw [a]; rfl)
  · rw [a]
    exact b

theorem Effect.single {foundation berkeley : Nat} {c : Command} {s t : ProofStore}
    (h : runProofCommand foundation berkeley runAxioms c s = some t) :
    Effect foundation berkeley [c] s t :=
  Or.inr (by simp [executeCommands, h])

def nips (n : Nat) : List Command := List.replicate n (.nip 0)

theorem nip_effect (foundation berkeley top head tail op cache : Nat) :
    Effect foundation berkeley [.nip 0] ⟨top, pair head tail, op, cache⟩
      ⟨top, tail, op, head⟩ := by
  unfold Effect
  by_cases eq : cache = 1
  · exact Or.inl (by simp [executeCommands, runProofCommand, eq])
  · exact Or.inr (by simp [executeCommands, runProofCommand, eq, decode_pair])

/-- Pop the specified prefix and leave its last formula in the cache. -/
theorem pop_to (foundation berkeley : Nat) (forms : List Nat)
    (top last tail op cache : Nat) :
    Effect foundation berkeley (nips (forms.length + 1))
      ⟨top, pushList (forms ++ [last]) tail, op, cache⟩
      ⟨top, tail, op, last⟩ := by
  induction forms generalizing cache with
  | nil => exact nip_effect foundation berkeley top last tail op cache
  | cons h hs ih =>
    have first := nip_effect foundation berkeley top h (pushList (hs ++ [last]) tail) op cache
    simpa [nips, List.replicate_succ, Nat.add_assoc] using first.then (ih h)

theorem ax_effect (foundation berkeley c x y formula : Nat) (s : ProofStore) :
    Effect foundation berkeley [.ax c x y formula] s
      (runAxioms c y formula { s with operand := s.operand + x }) :=
  Effect.single rfl

/-- Save the current top formula on the stack and reset the three
command-boundary registers. The operand is known when building the word. -/
def saveTop (op : Nat) : List Command :=
  [.ax op 0 0 0] ++ nips 9 ++ [.mp 0]

theorem saveTop_effect (foundation berkeley top stack op cache : Nat) :
    Effect foundation berkeley (saveTop op)
      ⟨top, stack, op, cache⟩ (neutral (pair top stack)) := by
  let hs := heads op cache op 0
  let generalized := all op cache
  have axiomStep : Effect foundation berkeley [.ax op 0 0 0] ⟨top, stack, op, cache⟩
      ⟨0, pushList (hs ++ [generalized]) (pair top stack), 0, 0⟩ := by
    apply Effect.single
    simp [runProofCommand, runAxioms, pushList, hs, generalized]
  have popped : Effect foundation berkeley (nips 9)
      ⟨0, pushList (hs ++ [generalized]) (pair top stack), 0, 0⟩
      ⟨0, pair top stack, 0, generalized⟩ :=
    pop_to foundation berkeley hs 0 generalized (pair top stack) 0 0
  have noMatch : generalized ≠ imp 0 0 := by
    change all op cache ≠ imp 0 0
    change 4 * pair op cache + 2 ≠ 0
    omega
  have clear : Effect foundation berkeley [.mp 0]
      ⟨0, pair top stack, 0, generalized⟩ (neutral (pair top stack)) := by
    apply Effect.single
    simp [runProofCommand, noMatch, neutral]
  exact axiomStep.then (popped.then clear)

/-- A word compiled for a formula pushes it and a known list of auxiliary
entries, while preserving the incoming stack below them. -/
def Pushes (foundation berkeley formula : Nat) : Prop :=
  ∃ word extras, ∀ tail, Effect foundation berkeley word
    (neutral tail) (neutral (pushList (formula :: extras) tail))

theorem pushes_truth (foundation berkeley : Nat) : Pushes foundation berkeley 0 := by
  exact ⟨saveTop 0, [], fun tail => saveTop_effect _ _ 0 tail 0 0⟩

theorem pushes_extra_foundation (foundation berkeley : Nat) : Pushes foundation berkeley foundation := by
  refine ⟨[.extra 0, .nip 0, .drop 0] ++ saveTop 0, [berkeley, 0], fun tail => ?_⟩
  have extra : Effect foundation berkeley [.extra 0] (neutral tail)
      ⟨berkeley, pair foundation (pair 0 tail), 0, 0⟩ :=
    Effect.single rfl
  have nip := nip_effect foundation berkeley berkeley foundation (pair 0 tail) 0 0
  have drop : Effect foundation berkeley [.drop 0] ⟨berkeley, pair 0 tail, 0, foundation⟩
      ⟨foundation, pair berkeley (pair 0 tail), 0, foundation⟩ := Effect.single rfl
  exact extra.then (nip.then (drop.then (saveTop_effect _ _ _ _ _ _)))

theorem pushes_extra_berkeley (foundation berkeley : Nat) : Pushes foundation berkeley berkeley := by
  refine ⟨[.extra 0] ++ saveTop 0, [foundation, 0], fun tail => ?_⟩
  have extra : Effect foundation berkeley [.extra 0] (neutral tail)
      ⟨berkeley, pair foundation (pair 0 tail), 0, 0⟩ := Effect.single rfl
  exact extra.then (saveTop_effect _ _ _ _ _ _)

theorem pushes_bundle (foundation berkeley : Nat) {a b c : Nat} (freshA : c ≠ a)
    (freshB : c ≠ b) : Pushes foundation berkeley (bundle a b c) := by
  refine ⟨[.ax c a b 0] ++ saveTop 0, heads a b c 0 ++ [all a 0, 0], fun tail => ?_⟩
  have start : runProofCommand foundation berkeley runAxioms (.ax c a b 0) (neutral tail) =
      some ⟨bundle a b c, pushList (heads a b c 0 ++ [all a 0, 0]) tail, 0, 0⟩ := by
    simp [runProofCommand, runAxioms, neutral, freshA, freshB, pushList]
  exact (Effect.single start).then (saveTop_effect _ _ _ _ _ _)

theorem pushes_head (foundation berkeley a b c x formula : Nat) (member : formula ∈ heads a b c x) :
    Pushes foundation berkeley formula := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  let gate := if c = a ∨ c = b then 0 else bundle a b c
  let extras := gate :: (after ++ [all a 0, 0])
  refine ⟨[.ax c a b x] ++ nips (before.length + 1) ++ [.drop 0] ++ saveTop 0, extras,
    fun tail => ?_⟩
  let saved := pushList (after ++ [all a 0, 0]) tail
  have first : Effect foundation berkeley [.ax c a b x] (neutral tail)
      ⟨gate, pushList (before ++ [formula]) saved, 0, 0⟩ := by
    apply Effect.single
    simp [runProofCommand, runAxioms, neutral, split, gate, saved, pushList_append, pushList]
  have pop := pop_to foundation berkeley before gate formula saved 0 0
  have drop : Effect foundation berkeley [.drop 0] ⟨gate, saved, 0, formula⟩
      ⟨formula, pair gate saved, 0, formula⟩ := Effect.single rfl
  have final := first.then (pop.then (drop.then (saveTop_effect _ _ _ _ _ _)))
  simpa only [List.append_assoc, extras, pushList_cons, saved] using final

/-- Generalization uses the proof saved by AX before its propositional
head and set-theoretic bundle are evaluated. -/
theorem pushes_generalize {foundation berkeley formula : Nat}
    (given : Pushes foundation berkeley formula) (label : Nat) :
    Pushes foundation berkeley (all label formula) := by
  obtain ⟨word, extras, compiled⟩ := given
  let generalized := all label formula
  refine ⟨word ++ [.nip 0, .ax label label 0 0] ++ nips 9 ++ [.drop 0] ++ saveTop 0,
    0 :: 0 :: extras, fun tail => ?_⟩
  let rest := pushList extras tail
  have cache := nip_effect foundation berkeley 0 formula rest 0 0
  have axStep : Effect foundation berkeley [.ax label label 0 0] ⟨0, rest, 0, formula⟩
      ⟨0, pushList (heads label formula label 0 ++ [generalized]) (pair 0 rest), 0, 0⟩ := by
    apply Effect.single
    simp [runProofCommand, runAxioms, generalized, pushList]
  have popped : Effect foundation berkeley (nips 9)
      ⟨0, pushList (heads label formula label 0 ++ [generalized]) (pair 0 rest), 0, 0⟩
      ⟨0, pair 0 rest, 0, generalized⟩ :=
    pop_to foundation berkeley (heads label formula label 0) 0 generalized (pair 0 rest) 0 0
  have drop : Effect foundation berkeley [.drop 0] ⟨0, pair 0 rest, 0, generalized⟩
      ⟨generalized, pair 0 (pair 0 rest), 0, generalized⟩ := Effect.single rfl
  have done := (compiled tail).then (cache.then (axStep.then (popped.then
    (drop.then (saveTop_effect _ _ _ _ _ _)))))
  simpa only [List.append_assoc, List.cons_append, List.nil_append, pushList_cons, rest, generalized] using done

/-- Modus ponens uses a predictable number of pops to reach the saved
implication under the antecedent and its auxiliary stack entries. -/
theorem pushes_mp {foundation berkeley premise conclusion : Nat}
    (antecedent : Pushes foundation berkeley premise)
    (implication : Pushes foundation berkeley (imp premise conclusion)) :
    Pushes foundation berkeley conclusion := by
  obtain ⟨anteWord, anteExtra, anteProof⟩ := antecedent
  obtain ⟨impWord, impExtra, impProof⟩ := implication
  refine ⟨impWord ++ anteWord ++ [.nip 0, .drop 0] ++
    nips ((0 :: anteExtra).length + 1) ++ [.mp conclusion] ++ saveTop conclusion,
    0 :: impExtra, fun tail => ?_⟩
  let savedImp := pushList (imp premise conclusion :: impExtra) tail
  let savedRest := pushList anteExtra savedImp
  have start := (impProof tail).then (anteProof savedImp)
  have getAnte := nip_effect foundation berkeley 0 premise savedRest 0 0
  have expose : Effect foundation berkeley [.drop 0] ⟨0, savedRest, 0, premise⟩
      ⟨premise, pair 0 savedRest, 0, premise⟩ := Effect.single rfl
  have getImp := pop_to foundation berkeley (0 :: anteExtra) premise (imp premise conclusion)
    (pushList impExtra tail) 0 premise
  have mp : Effect foundation berkeley [.mp conclusion]
      ⟨premise, pushList impExtra tail, 0, imp premise conclusion⟩
      ⟨conclusion, pair 0 (pushList impExtra tail), conclusion, 0⟩ := by
    apply Effect.single
    simp [runProofCommand]
  have readImp : Effect foundation berkeley (nips ((0 :: anteExtra).length + 1))
      ⟨premise, pair 0 savedRest, 0, premise⟩
      ⟨premise, pushList impExtra tail, 0, imp premise conclusion⟩ := by
    simpa [savedRest, savedImp, pushList_append] using getImp
  have done := start.then (getAnte.then (expose.then (readImp.then
    (mp.then (saveTop_effect _ _ _ _ _ _)))))
  simpa only [List.append_assoc, List.cons_append, List.nil_append, pushList_cons] using done

end I0451.Logic
