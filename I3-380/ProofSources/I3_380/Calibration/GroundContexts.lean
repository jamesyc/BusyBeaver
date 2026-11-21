module
public import I3_380.Calibration.GroundTerms
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceWords

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The token vectors to either side of a single hole in a prefix word. -/
structure Context (M : Type) where
  before : M
  after : M

noncomputable def Context.fill (c : Context M) (body : M) : M :=
  appendVector c.before (appendVector body c.after)

noncomputable def Context.compose (outer inner : Context M) : Context M :=
  ⟨appendVector outer.before inner.before,appendVector inner.after outer.after⟩

theorem Context.compose_fill (outer inner : Context M) (body : M) :
    (outer.compose inner).fill body = outer.fill (inner.fill body) := by
  simp only [Context.compose,Context.fill,appendVector_assoc]

theorem Context.blank_fill (body : M) : (Context.mk 0 0).fill body = body := by
  simp [Context.fill]

theorem flatten_at {n : Nat} (vectors : Fin n → M) (index : Fin n) :
    ∃ c : Context M, ∀ vector : M,
      flattenTokens (matrixToVec (Function.update vectors index vector)) = c.fill vector := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) index
    · refine ⟨⟨0,flattenTokens (matrixToVec (Fin.tail vectors))⟩,fun vector => ?_⟩
      rw [show matrixToVec (Function.update vectors 0 vector) =
          Function.update vectors 0 vector 0 ∷ matrixToVec (Fin.tail (Function.update vectors 0 vector)) from rfl]
      simp only [Function.update_self,Fin.tail_update_zero,flattenTokens_cons,Context.fill,appendVector_nil]
    · obtain ⟨c,hole⟩ := ih (Fin.tail vectors) i
      refine ⟨⟨appendVector (vectors 0) c.before,c.after⟩,fun vector => ?_⟩
      rw [show matrixToVec (Function.update vectors i.succ vector) =
          Function.update vectors i.succ vector 0 ∷ matrixToVec (Fin.tail (Function.update vectors i.succ vector))
        from rfl]
      simp only [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i)),Fin.tail_update_succ,flattenTokens_cons,
        hole,Context.fill,appendVector_assoc]

private theorem oneToken {n : Nat} (symbol : FunctionSymbol n) : ∃ t : M,
    ∀ args : Fin n → GroundTerm M,
      termTokens (application symbol args).val = t ∷ flattenTokens (matrixToVec (fun i => termTokens (args i).val)) :=
  ⟨_,application_tokens symbol⟩

/-- Replacing the given argument changes exactly one contiguous span
of the prefix word. The span can be internally finite and nonstandard. -/
theorem application_context {n : Nat} (symbol : FunctionSymbol n) (args : Fin n → GroundTerm M)
    (index : Fin n) :
    ∃ c : Context M, ∀ x : GroundTerm M,
      termTokens (application symbol (Function.update args index x)).val = c.fill (termTokens x.val) := by
  let tokens := fun x : GroundTerm M => termTokens x.val
  obtain ⟨head,app⟩ := oneToken (M := M) symbol
  obtain ⟨c,argument⟩ := flatten_at (tokens ∘ args) index
  refine ⟨⟨head ∷ c.before,c.after⟩,fun x => ?_⟩
  rw [app]
  change head ∷ flattenTokens (matrixToVec (tokens ∘ Function.update args index x)) = _
  rw [Function.comp_update,argument]
  simp only [Context.fill,appendVector_cons,tokens]

theorem Context.fill_word (c : Context M) (body remainder : M) :
    emitVector (c.fill body) remainder =
      emitVector c.before (emitVector body (emitVector c.after remainder)) := by
  simp only [Context.fill,emitVector_append]

end PalomarI3380.Calibration.TermWords
