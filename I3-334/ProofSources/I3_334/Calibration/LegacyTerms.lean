module
public import I3_334.Calibration.LegacySemantics
public import I3_334.Calibration.LegacyStack
public import I3_334Support.Arithmetic.SchedulerMeasure
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380
open PalomarI3380.Calibration (FilterLanguage FunctionSymbol)
open PalomarI3380.Calibration.TermWords
open PalomarI3380.Compiler.Source (definableAllCons)
open ArithmeticMachine.SourceWords
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem oldFunction_of_code {arity tag : M} (ok : FilterLanguage.IsFunc arity tag) :
    ∃ n : Nat, ∃ f : FunctionSymbol n, arity = (n : M) ∧
      tag = (⌜(show FilterLanguage.Func n from f)⌝ : M) := by
  have bounds : arity < (4 : M) ∧ tag < (7 : M) := by
    have shape : (arity = 0 ∧ tag < 7) ∨ (arity = 1 ∧ tag < 4) ∨
        (arity = 2 ∧ tag < 2) ∨ (arity = 3 ∧ tag < 1) := by
      rw [isFunc_def] at ok
      let boundsDef : 𝚺ᴬ₀.Semisentence 2 :=
        .mkSigma “k c. (k = 0 ∧ c < 7) ∨ (k = 1 ∧ c < 4) ∨ (k = 2 ∧ c < 2) ∨ (k = 3 ∧ c < 1)”
      change boundsDef.val.Evalb ![arity,tag] at ok
      simpa [boundsDef,numeral_eq_natCast,Nat.cast_ofNat] using ok
    rcases shape with ⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨rfl,h⟩
    · exact ⟨by exact_mod_cast (show (0 : Nat) < 4 by decide),h⟩
    · exact ⟨by exact_mod_cast (show (1 : Nat) < 4 by decide),
        h.trans (by exact_mod_cast (show (4 : Nat) < 7 by decide))⟩
    · exact ⟨by exact_mod_cast (show (2 : Nat) < 4 by decide),
        h.trans (by exact_mod_cast (show (2 : Nat) < 7 by decide))⟩
    · exact ⟨by exact_mod_cast (show (3 : Nat) < 4 by decide),
        h.trans (by exact_mod_cast (show (1 : Nat) < 7 by decide))⟩
  obtain ⟨n,rfl⟩ := eq_nat_of_lt_nat (n := 4) bounds.1
  obtain ⟨t,rfl⟩ := eq_nat_of_lt_nat (n := 7) bounds.2
  obtain ⟨f,rfl⟩ := isFunc_quote_quote.mp ok
  exact ⟨n,f,rfl,rfl⟩

theorem termArguments {n : Nat} {raw : M} (typed : IsSemitermVec FilterLanguage (n : M) 0 raw) :
    ∃ args : Fin n → GroundTerm M, raw = matrixToVec (fun i => (args i).val) := by
  let args (i : Fin n) : GroundTerm M := ⟨raw.[(i.val : M)],typed.nth (by exact_mod_cast i.isLt)⟩
  refine ⟨args,nth_ext' (n : M) typed.lh (matrixToVec_len _) ?_⟩
  intro i bound
  obtain ⟨k,rfl⟩ := eq_nat_of_lt_nat bound
  have lt : k < n := by exact_mod_cast bound
  exact (matrixToVec_nth (fun j => (args j).val) (⟨k,lt⟩ : Fin n)).symm

theorem popStack_append_matrix {n : Nat} (values : Fin n → M) (stack : M) :
    popStack n (appendVector (matrixToVec values) stack) = stack := by
  induction n with
  | zero => simp [popStack]
  | succ n ih =>
    simp only [matrixToVec_succ,appendVector_cons,popStack,stackTail_cons]
    exact ih (Matrix.vecTail values)

theorem nth_append_matrix {n : Nat} (values : Fin n → M) (stack : M) (i : Fin n) :
    (appendVector (matrixToVec values) stack).[(i.val : M)] = values i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp [Matrix.vecHead]
    | succ i =>
      simpa only [matrixToVec_succ,appendVector_cons,Fin.val_succ,Nat.cast_succ,nth_adjoin_succ,
        Matrix.vecTail,Function.comp_apply] using ih (Matrix.vecTail values) i

theorem legacyStackApply_append_matrix {n : Nat} (f : FunctionSymbol n) (values : Fin n → M) (stack : M) :
    legacyStackApply f (appendVector (matrixToVec values) stack) = legacyApplication f values ∷ stack := by
  have enough : (n : M) ≤ len (appendVector (matrixToVec values) stack) := by
    simp only [appendVector_length,matrixToVec_len]
    exact le_add_of_nonneg_right (Arithmetic.zero_le _)
  unfold legacyStackApply
  rw [if_pos enough,popStack_append_matrix]
  have agrees : (fun i : Fin n => (appendVector (matrixToVec values) stack).[(i.val : M)]) = values :=
    funext (nth_append_matrix values stack)
  rw [agrees]

theorem legacyFold_forest {n : Nat} (tokens values : Fin n → M)
    (push : ∀ i stack, legacyFold (tokens i) stack = values i ∷ stack) (stack : M) :
    legacyFold (flattenTokens (matrixToVec tokens)) stack = appendVector (matrixToVec values) stack := by
  induction n generalizing stack with
  | zero => simp
  | succ n ih =>
    simp only [matrixToVec_succ,flattenTokens_cons,legacyFold_append]
    have first := push 0
    have tail := ih (Matrix.vecTail tokens) (Matrix.vecTail values)
      (fun i stack => push i.succ stack) stack
    rw [tail,show Matrix.vecHead tokens = tokens 0 from rfl,first,appendVector_cons]
    rfl

noncomputable def legacyEval (term : M) : M := (legacyFold (termTokens term) 0).[0]

theorem legacyEval_definable : 𝚺ᴬ_[2]-Function₁ (legacyEval (M := M)) := by
  have fold := legacyFold_definable (M := M)
  have tokens : 𝚺ᴬ_[2]-Function₁ (termTokens (M := M)) := termTokens_definable.of_lt (by decide)
  change 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => v 0 = legacyEval (v 1))
  unfold legacyEval
  definability

def PushesLegacy (term : M) : Prop :=
  ValidLegacy (legacyEval term) ∧ ∀ s, legacyFold (termTokens term) s = legacyEval term ∷ s

theorem pushesLegacy_definable : 𝚷ᴬ_[3]-Predicate (PushesLegacy (M := M)) := by
  have valid : 𝚺ᴬ_[2]-Predicate (ValidLegacy (M := M)) := validLegacy_definable.of_lt (by decide)
  have folded := legacyFold_definable (M := M)
  have scalar := legacyEval_definable (M := M)
  have tokens : 𝚺ᴬ_[2]-Function₁ (termTokens (M := M)) := termTokens_definable.of_lt (by decide)
  have good : 𝚺ᴬ_[2]-Predicate (fun t : M => ValidLegacy (legacyEval t)) := by definability
  have eq : 𝚺ᴬ_[2]-Relation (fun s t : M => legacyFold (termTokens t) s = legacyEval t ∷ s) := by
    definability
  exact (good.of_lt (by decide)).and (definableAllCons (eq.of_lt (by decide)))

theorem pushesLegacy_of_calculation {t a : M} (good : ValidLegacy a)
    (step : ∀ s, legacyFold (termTokens t) s = a ∷ s) : PushesLegacy t := by
  have value : legacyEval t = a := by rw [legacyEval,step,nth_adjoin_zero]
  exact ⟨value ▸ good,by simpa only [value] using step⟩

theorem legacyFold_application {n : Nat} (symbol : FunctionSymbol n) (args : Fin n → GroundTerm M)
    (valid : ∀ i, PushesLegacy (args i).val) (stack : M) :
    legacyFold (termTokens (application symbol args).val) stack =
      legacyApplication symbol (fun i => legacyEval (args i).val) ∷ stack := by
  rw [application_tokens,← show oldToken symbol =
      (⟪(n : M),(⌜(show FilterLanguage.Func n from symbol)⌝ : M)⟫ : M) from rfl,
    legacyFold_cons]
  have prep := legacyFold_forest (fun i => termTokens (args i).val) (fun i => legacyEval (args i).val)
    (fun i => (valid i).2) stack
  rw [prep,legacyStackApply_append_matrix]

theorem pushesLegacy_application {n : Nat} (symbol : FunctionSymbol n) (args : Fin n → GroundTerm M)
    (valid : ∀ i, PushesLegacy (args i).val) :
    PushesLegacy (application symbol args).val :=
  pushesLegacy_of_calculation
    (legacyApplication_valid symbol _ (fun i => (valid i).1)) (legacyFold_application symbol args valid)

theorem pushesLegacy (t : GroundTerm M) : PushesLegacy t.val := by
  have coded : 𝚺ᴬ_[3]-Relation (IsSemiterm (V := M) FilterLanguage) := IsSemiterm.definable.of_deltaOne
  have source : 𝚺ᴬ_[3]-Predicate (fun x : M => IsSemiterm FilterLanguage 0 x) :=
    coded.comp (Bounding.HierarchySymbol.DefinableFunction.const 0)
      (Bounding.HierarchySymbol.DefinableFunction.var 0)
  have form : 𝚷ᴬ_[3]-Predicate (fun x : M => IsSemiterm FilterLanguage 0 x → PushesLegacy x) :=
    source.imp (Γ := 𝚷) pushesLegacy_definable
  refine InductionOnHierarchy.order_induction_sigma 𝚷 3 form ?_ t.val t.isSemiterm
  intro code ih typed
  rcases typed.case with ⟨i,below,_⟩ | ⟨i,rfl⟩ | ⟨arity,tag,children,known,valid,rfl⟩
  · exact (not_lt_of_ge (Arithmetic.zero_le i) below).elim
  · apply pushesLegacy_of_calculation (legacyConstant_valid (M := M) .D)
    intro stack
    rw [termTokens,termConstruction.result_fvar]
    have token : termConstruction.fvar (![] : Fin 0 → M) i = oldToken (M := M) (.constant .D) ∷ 0 := by
      have tag : Encodable.encode (show FilterLanguage.Func 0 from FunctionSymbol.constant .D) = 1 := by decide
      unfold oldToken
      change (⟪0,1⟫ : M) ∷ 0 = (⟪(0 : Nat),((Encodable.encode
        (show FilterLanguage.Func 0 from FunctionSymbol.constant .D)) : M)⟫ : M) ∷ 0
      rw [tag,Nat.cast_zero,Nat.cast_one]
    rw [token,legacyFold_cons,legacyFold_nil]
    simp [legacyStackApply,popStack,legacyApplication,Arithmetic.zero_le]
  · obtain ⟨n,symbol,rfl,rfl⟩ := oldFunction_of_code known
    obtain ⟨args,codeForm⟩ := termArguments valid
    have app : (^func (n : M) (⌜(show FilterLanguage.Func n from symbol)⌝ : M) children) =
        (application symbol args).val := congrArg _ codeForm
    rw [app]
    apply pushesLegacy_application symbol args
    intro i
    have childEq := matrixToVec_nth (fun j => (args j).val) i
    rw [← codeForm] at childEq
    have smaller : children.[(i.val : M)] < ^func (n : M)
        (⌜(show FilterLanguage.Func n from symbol)⌝ : M) children :=
      nth_lt_qqFunc_of_lt (by rw [valid.lh]; exact_mod_cast i.isLt)
    exact ih _ (childEq ▸ smaller) (args i).isSemiterm

theorem legacyEval_application {n : Nat} (symbol : FunctionSymbol n) (args : Fin n → GroundTerm M) :
    legacyEval (application symbol args).val = legacyApplication symbol (fun i => legacyEval (args i).val) := by
  rw [legacyEval,legacyFold_application symbol args (fun i => pushesLegacy (args i)),nth_adjoin_zero]

theorem legacyEval_term {V : Type} (args : V → GroundTerm M) (t : PalomarI3380.Term V) :
    legacyValue (legacyEval (groundAlgebra.eval args t).val) =
      legacyModel.eval (fun i => legacyValue (legacyEval (args i).val)) t := by
  induction t <;> simp only [Algebra.eval,groundAlgebra] at *
  all_goals
    rw [legacyEval_application,legacyApplication_value _ _ (fun i => (pushesLegacy _).1)]
    simp only [legacyAlgebraApply,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, *]

end PalomarI3334.SearchProgram
