module
public import I3_334Support.Search.Arithmetic.SourceWords
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.SourceWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable def consDef : 𝚺ᴬ₁.Semisentence 4 :=
  .mkSigma “out arity tag rest. ∃ suffix,
    !SourceCantor.pairGraph suffix tag rest ∧ !SourceCantor.pairGraph out (arity+1) suffix”

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem consDef_eval (out a t w : M) :
    consDef.val.Evalb ![out,a,t,w] ↔ out = cons a t w := by
  simp [consDef,cons,SourceCantor.pair_graph]

def appendBlueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “out suffix. out = suffix”
  adjoin := .mkSigma “out first rest previous suffix. !adjoinDef out first previous”

noncomputable def appendConstruction : VecRec.Construction M appendBlueprint where
  nil args := args 0
  adjoin (_ first _ previous) := first ∷ previous
  nil_defined := .mk fun v => by simp [appendBlueprint]
  adjoin_defined := .mk fun v => by simp [appendBlueprint]

/-- Concatenation of internal vectors. The vector may have a
nonstandard number of entries. -/
noncomputable def appendVector (front suffix : M) : M :=
  appendConstruction.result ![suffix] front

theorem appendVector_eval (out front suffix : M) :
    appendBlueprint.resultDef.val.Evalb ![out,front,suffix] ↔ out = appendVector front suffix := by
  exact appendConstruction.result_defined.iff

@[simp] theorem appendVector_nil (suffix : M) : appendVector 0 suffix = suffix := by
  simp [appendVector,appendConstruction]

@[simp] theorem appendVector_cons (head front suffix : M) :
    appendVector (head ∷ front) suffix = head ∷ appendVector front suffix := by
  simp [appendVector,appendConstruction]

@[definability] instance appendVector_definable : 𝚺ᴬ₁-Function₂ (appendVector (M := M)) :=
  (appendConstruction.result_defined (V := M)).to_definable

@[simp] theorem appendVector_empty_suffix (front : M) : appendVector front 0 = front := by
  induction front using adjoin_ISigma1.sigma1_succ_induction with
  | nil => simp
  | adjoin first rest ih => simp [ih]
  | hP => definability

theorem appendVector_assoc (a b c : M) :
    appendVector (appendVector a b) c = appendVector a (appendVector b c) := by
  induction a using adjoin_ISigma1.sigma1_succ_induction with
  | nil => simp
  | adjoin first rest ih => simp [ih]
  | hP => definability

@[simp] theorem appendVector_length (front back : M) :
    len (appendVector front back) = len front + len back := by
  induction front using adjoin_ISigma1.sigma1_succ_induction with
  | nil => simp
  | adjoin first rest ih => simp [ih,add_assoc,add_left_comm,add_comm]
  | hP => definability

/-- Concatenate the token vectors of the arguments in their source order. -/
def flattenBlueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “out. out = 0”
  adjoin := .mkSigma “out vector rest emitted. !(appendBlueprint.resultDef) out vector emitted”

noncomputable def flattenConstruction : VecRec.Construction M flattenBlueprint where
  nil _ := 0
  adjoin (_ vector _ emitted) := appendVector vector emitted
  nil_defined := .mk fun v => by simp [flattenBlueprint]
  adjoin_defined := .mk fun v => by
    simpa [flattenBlueprint,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
      Empty.eq_elim,Matrix.empty_eq,Matrix.constant_eq_singleton] using
      appendVector_eval (v 0) (v 1) (v 3)

noncomputable def flattenTokens (vectors : M) : M :=
  flattenConstruction.result ![] vectors

@[simp] theorem flattenTokens_zero : flattenTokens (0 : M) = 0 := by
  simp [flattenTokens,flattenConstruction]

@[simp] theorem flattenTokens_cons (head tail : M) :
    flattenTokens (head ∷ tail) = appendVector head (flattenTokens tail) := by
  simp [flattenTokens,flattenConstruction]

@[definability] instance flattenTokens_definable : 𝚺ᴬ₁-Function₁ (flattenTokens (M := M)) :=
  (flattenConstruction.result_defined (V := M)).to_definable

noncomputable def emissionBlueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “out suffix. out = suffix”
  adjoin := .mkSigma “out token rest previous suffix. ∃ a t,
    !pairDef token a t ∧ !consDef out a t previous”

noncomputable def emissionConstruction : VecRec.Construction M emissionBlueprint where
  nil args := args 0
  adjoin (_ token _ previous) := cons (π₁ token) (π₂ token) previous
  nil_defined := .mk fun v => by simp [emissionBlueprint]
  adjoin_defined := .mk fun v => by
    simp [emissionBlueprint,pair_defined.iff,consDef_eval]
    constructor
    · rintro ⟨a,t,token,returned⟩
      simpa [token] using returned
    · intro returned
      exact ⟨π₁ (v 1),π₂ (v 1),(pair_unpair (v 1)).symm,returned⟩

/-- Serialize a vector of tokens into the released positive-arity word
format, followed by the given numeric suffix. -/
noncomputable def emitVector (tokens suffix : M) : M :=
  emissionConstruction.result ![suffix] tokens

@[simp] theorem emitVector_nil (suffix : M) : emitVector 0 suffix = suffix := by
  simp [emitVector,emissionConstruction]

@[simp] theorem emitVector_cons (token tokens suffix : M) :
    emitVector (token ∷ tokens) suffix = cons (π₁ token) (π₂ token) (emitVector tokens suffix) := by
  simp [emitVector,emissionConstruction]

@[definability] instance emitVector_definable : 𝚺ᴬ₁-Function₂ (emitVector (M := M)) :=
  (emissionConstruction.result_defined (V := M)).to_definable

theorem emitVector_append (front back suffix : M) :
    emitVector (appendVector front back) suffix = emitVector front (emitVector back suffix) := by
  induction front using adjoin_ISigma1.sigma1_succ_induction with
  | nil => simp
  | adjoin token front ih => simp [ih]
  | hP => definability

theorem emitVector_nonempty {v : M} (nonempty : v ≠ 0) (suffix : M) :
    0 < emitVector v suffix := by
  rcases nil_or_adjoin v with zero | ⟨token,rest,eq⟩
  · exact (nonempty zero).elim
  · rw [eq,emitVector_cons]
    exact cons_positive ..

theorem emitVector_arity (token tokens suffix : M) :
    arity (emitVector (token ∷ tokens) suffix) = π₁ token := by simp

theorem emitVector_tag (token tokens suffix : M) :
    tag (emitVector (token ∷ tokens) suffix) = π₂ token := by simp

theorem emitVector_tail (token tokens suffix : M) :
    tail (emitVector (token ∷ tokens) suffix) = emitVector tokens suffix := by simp

end PalomarI3380.ArithmeticMachine.SourceWords
