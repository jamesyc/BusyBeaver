module
public import I3_334Support.Search.Arithmetic.WordEmission
public import I3_334Support.Arithmetic.FiniteTraces
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380.ArithmeticMachine.SourceWords (appendVector appendVector_definable)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- A fold of an arithmetic vector from right to left. The trace is
itself an arithmetic vector and can have nonstandard length. -/
def FoldPrefix (step : M → M → M) (word start count trace : M) : Prop :=
  len trace = count+1 ∧ trace.[0] = start ∧
    ∀ i < count, trace.[i+1] = step word.[len word-(i+1)] trace.[i]

theorem foldPrefix_definable {step : M → M → M} (defStep : 𝚺ᴬ_[2]-Function₂ step) :
    𝚺ᴬ_[2]-Relation₄ (FoldPrefix step) := by
  letI := defStep
  unfold FoldPrefix
  definability

theorem FoldPrefix.base (step : M → M → M) (word start : M) : FoldPrefix step word start 0 (?[start]) := by
  refine ⟨by simp,by simp,?_⟩
  intro i below
  exact (not_lt_of_ge (Arithmetic.zero_le i) below).elim

theorem FoldPrefix.extend {step : M → M → M} {word start count trace : M}
    (run : FoldPrefix step word start count trace) :
    FoldPrefix step word start (count+1)
      (concat trace (step word.[len word-(count+1)] trace.[count])) := by
  let next := step word.[len word-(count+1)] trace.[count]
  have index : count < len trace := by rw [run.1]; exact lt_add_one _
  have nonempty : (0 : M) < len trace := (Arithmetic.zero_le _).trans_lt index
  refine ⟨by rw [len_concat,run.1], by rw [concat_nth_lt _ _ nonempty,run.2.1],?_⟩
  intro i below
  rcases lt_or_eq_of_le (lt_succ_iff_le.mp below) with before | same
  · have after : i+1 < len trace := (succ_le_iff_lt.mpr before).trans_lt index
    rw [concat_nth_lt _ _ after,concat_nth_lt _ _ (before.trans index),run.2.2 _ before]
  · subst i
    change (concat trace next).[count+1] = step word.[len word-(count+1)] (concat trace next).[count]
    rw [concat_nth_len' _ _ run.1,concat_nth_lt _ _ index]

theorem foldPrefix_exists {step : M → M → M} (defStep : 𝚺ᴬ_[2]-Function₂ step) (word start count : M) :
    ∃ trace, FoldPrefix step word start count trace := by
  let P := fun n : M => ∃ trace, FoldPrefix step word start n trace
  have definition : 𝚺ᴬ_[2]-Predicate P := by
    have rel := foldPrefix_definable defStep
    unfold P
    definability
  exact InductionOnHierarchy.succ_induction_sigma 𝚺 2 definition ⟨_,FoldPrefix.base step word start⟩
    (fun _ ⟨_, h⟩ => ⟨_,h.extend⟩) count

theorem FoldPrefix.same {step : M → M → M} {word start m n a b : M}
    (left : FoldPrefix step word start m a) (right : FoldPrefix step word start n b) :
    ∀ i ≤ m, i ≤ n → a.[i] = b.[i] := by
  let P := fun i : M => i ≤ m → i ≤ n → a.[i] = b.[i]
  have definition : 𝚺ᴬ₁-Predicate P := by unfold P; definability
  apply ISigma1.sigma1_succ_induction (P := P) definition
  · intro _ _
    rw [left.2.1,right.2.1]
  · intro i ih leM leN
    have bm := succ_le_iff_lt.mp leM
    have bn := succ_le_iff_lt.mp leN
    exact (left.2.2 i bm).trans (by rw [ih (le_of_lt bm) (le_of_lt bn),← right.2.2 i bn])

noncomputable def modelFold (step : M → M → M) (graph : 𝚺ᴬ_[2]-Function₂ step) (word start : M) : M :=
  (Classical.choose (foldPrefix_exists graph word start (len word))).[len word]

theorem modelFold_of_trace {step : M → M → M} (graph : 𝚺ᴬ_[2]-Function₂ step)
    {word start trace : M} (run : FoldPrefix step word start (len word) trace) :
    modelFold step graph word start = trace.[len word] :=
  (Classical.choose_spec (foldPrefix_exists graph word start (len word))).same run _ le_rfl le_rfl

theorem modelFold_definable {step : M → M → M} (graph : 𝚺ᴬ_[2]-Function₂ step) :
    𝚺ᴬ_[2]-Function₂ (modelFold step graph) := by
  have relation := foldPrefix_definable graph
  have form : 𝚺ᴬ_[2].Definable (fun v : Fin 3 → M =>
      ∃ trace, FoldPrefix step (v 1) (v 2) (len (v 1)) trace ∧ v 0 = trace.[len (v 1)]) := by
    definability
  exact form.of_iff (fun v => by
    constructor
    · intro eq
      obtain ⟨trace,run⟩ := foldPrefix_exists graph (v 1) (v 2) (len (v 1))
      exact ⟨trace, run, eq.trans (modelFold_of_trace graph run)⟩
    · rintro ⟨trace,run,eq⟩
      exact eq.trans (modelFold_of_trace graph run).symm)

@[simp] theorem modelFold_nil {step : M → M → M} (graph : 𝚺ᴬ_[2]-Function₂ step) (start : M) :
    modelFold step graph 0 start = start := by
  have run := FoldPrefix.base step (0 : M) start
  have value := modelFold_of_trace graph (word := 0) (by simpa only [len_nil] using run)
  exact value.trans (by rw [len_nil]; exact nth_adjoin_zero ..)

@[simp] theorem modelFold_adjoin {step : M → M → M} (graph : 𝚺ᴬ_[2]-Function₂ step) (head word start : M) :
    modelFold step graph (head ∷ word) start = step head (modelFold step graph word start) := by
  obtain ⟨trace,h⟩ := foldPrefix_exists graph word start (len word)
  have beginning : FoldPrefix step (head ∷ word) start (len word) trace := by
    refine ⟨h.1,h.2.1,?_⟩
    intro i below
    have needed : (head ∷ word).[len (head ∷ word)-(i+1)] = word.[len word-(i+1)] := by
      have le := succ_le_iff_lt.mpr below
      rw [len_adjoin,add_comm (len word) 1,add_comm i 1,add_tsub_add_eq_tsub_left]
      have sub : len word-i = (len word-(i+1))+1 := by
        have bind := tsub_add_cancel_of_le le
        calc
          len word-i = ((len word-(i+1))+(i+1))-i := by rw [bind]
          _ = (len word-(i+1))+1 := by rw [← add_assoc,add_right_comm,Arithmetic.add_sub_self]
      rw [sub,nth_adjoin_succ,add_comm i 1]
    rw [needed]
    exact h.2.2 i below
  have appended := beginning.extend
  have size := len_adjoin head word
  have full : FoldPrefix step (head ∷ word) start (len (head ∷ word))
      (concat trace (step (head ∷ word).[len (head ∷ word)-(len word+1)] trace.[len word])) :=
    size.symm ▸ appended
  rw [modelFold_of_trace graph full,concat_nth_len' _ _ (h.1.trans size.symm)]
  have index : len (head ∷ word)-(len word+1) = 0 := by rw [size,Arithmetic.sub_self]
  rw [index,nth_adjoin_zero,modelFold_of_trace graph h]

/-- The PA induction rule for arithmetic vectors and a higher definable predicate. -/
theorem modelVector_induction {P : M → Prop} (definition : 𝚷ᴬ_[3]-Predicate P)
    (empty : P 0) (step : ∀ head tail : M, P tail → P (head ∷ tail)) (x : M) : P x :=
  InductionOnHierarchy.order_induction_sigma 𝚷 3 definition
    (fun word ih => by
      rcases nil_or_adjoin word with rfl | ⟨head,tail,rfl⟩
      · exact empty
      · exact step head tail (ih tail (lt_adjoin' _ _))) x

theorem modelFold_append {step : M → M → M} (graph : 𝚺ᴬ_[2]-Function₂ step) (a b start : M) :
    modelFold step graph (appendVector a b) start =
      modelFold step graph a (modelFold step graph b start) := by
  letI foldDef : 𝚺ᴬ_[2]-Function₂ (modelFold step graph) := modelFold_definable graph
  letI appendDef : 𝚺ᴬ_[2]-Function₂ (appendVector (M := M)) :=
    appendVector_definable.of_lt (by decide)
  let P := fun x => modelFold step graph (appendVector x b) start =
      modelFold step graph x (modelFold step graph b start)
  have prefixDef : 𝚺ᴬ_[2].DefinableFunction (fun v : Fin 1 → M => appendVector (v 0) b) :=
    Bounding.HierarchySymbol.DefinableFunction₂.comp (F := appendVector) (.var 0) (.const b)
  have left : 𝚺ᴬ_[2].DefinableFunction (fun v : Fin 1 → M => modelFold step graph (appendVector (v 0) b) start) :=
    Bounding.HierarchySymbol.DefinableFunction₂.comp (F := modelFold step graph) prefixDef (.const start)
  have right : 𝚺ᴬ_[2].DefinableFunction (fun v : Fin 1 → M => modelFold step graph (v 0) (modelFold step graph b start)) :=
    Bounding.HierarchySymbol.DefinableFunction₂.comp (F := modelFold step graph) (.var 0) (.const _)
  have equal : 𝚺ᴬ_[2]-Relation (fun a b : M => a = b) := by definability
  have prop : 𝚺ᴬ_[2]-Predicate P := equal.comp left right
  refine modelVector_induction (P := P) (prop.of_lt (by decide)) ?_ ?_ a
  · change modelFold step graph (appendVector 0 b) start = modelFold step graph 0 (modelFold step graph b start)
    rw [PalomarI3380.ArithmeticMachine.SourceWords.appendVector_nil,modelFold_nil]
  · intro h t ih
    change modelFold step graph (appendVector (h ∷ t) b) start =
      modelFold step graph (h ∷ t) (modelFold step graph b start)
    rw [PalomarI3380.ArithmeticMachine.SourceWords.appendVector_cons,modelFold_adjoin,modelFold_adjoin]
    exact congrArg (step h) ih

end PalomarI3334.SearchProgram
