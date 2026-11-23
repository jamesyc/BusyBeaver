module
public import I3_334.Calibration.LegacyTerms
public import I3_334Support.Calibration.GroundCongruence
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380
open PalomarI3380.Arithmetic (Chain)
open PalomarI3380.Calibration (FunctionSymbol)
open PalomarI3380.Calibration.TermWords
open PalomarI3380.Compiler.Source (definableAllCons)
open ArithmeticMachine.SourceWords (appendVector)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def LegacyAgreement (a b : M) : Prop :=
  ValidLegacy a ∧ ValidLegacy b ∧
    ModelDerives (π₁ a) (π₁ b) ∧ (π₂ a = 0 ↔ π₂ b = 0)

theorem legacyAgreement_definable : 𝚺ᴬ₁-Relation (LegacyAgreement (M := M)) := by
  have typed := validLegacy_definable (M := M)
  have rewrites := modelDerives_definable (M := M)
  unfold LegacyAgreement
  definability

theorem legacyAgreement_iff {a b : M} :
    LegacyAgreement a b ↔ ValidLegacy a ∧ ValidLegacy b ∧ legacyValue a = legacyValue b := by
  constructor
  · rintro ⟨ha,hb,derives,bit⟩
    refine ⟨ha,hb,Prod.ext ?_ ?_⟩
    · change legacyNative (π₁ a) = legacyNative (π₁ b)
      rw [legacyNative_valid ha,legacyNative_valid hb]
      exact Subtype.ext (modelClass_eq.mpr derives)
    · change decide (π₂ a ≠ 0) = decide (π₂ b ≠ 0)
      by_cases ha : π₂ a = 0 <;> simp [ha,← bit]
  · rintro ⟨ha,hb,same⟩
    have eq := congrArg (fun x : ClosedClass M × Bool => x.1.val) same
    change (legacyNative (π₁ a)).val = (legacyNative (π₁ b)).val at eq
    rw [legacyNative_valid ha,legacyNative_valid hb] at eq
    have bit := congrArg Prod.snd same
    change decide (π₂ a ≠ 0) = decide (π₂ b ≠ 0) at bit
    refine ⟨ha,hb,modelClass_eq.mp eq,?_⟩
    by_cases x : π₂ a = 0 <;> by_cases y : π₂ b = 0 <;> simp_all

theorem LegacyAgreement.refl {a : M} (h : ValidLegacy a) : LegacyAgreement a a :=
  ⟨h,h,ModelDerives.refl _,Iff.rfl⟩

theorem LegacyAgreement.trans {a b c : M} (h : LegacyAgreement a b) (k : LegacyAgreement b c) :
    LegacyAgreement a c :=
  ⟨h.1,k.2.1,h.2.2.1.trans k.2.2.1,h.2.2.2.trans k.2.2.2⟩

theorem LegacyAgreement.application {n : Nat} (f : FunctionSymbol n) {a b : Fin n → M}
    (args : ∀ i, LegacyAgreement (a i) (b i)) : LegacyAgreement (legacyApplication f a) (legacyApplication f b) := by
  have ha := fun i => (args i).1
  have hb := fun i => (args i).2.1
  apply legacyAgreement_iff.mpr
  refine ⟨legacyApplication_valid f a ha,legacyApplication_valid f b hb,?_⟩
  rw [legacyApplication_value f a ha,legacyApplication_value f b hb]
  exact congrArg (legacyAlgebraApply f) (funext (fun i => (legacyAgreement_iff.mp (args i)).2.2))

def StackAgreement (a b : M) : Prop :=
  len a = len b ∧ ∀ i < len a, LegacyAgreement a.[i] b.[i]

theorem stackAgreement_definable : 𝚺ᴬ₁-Relation (StackAgreement (M := M)) := by
  have good := legacyAgreement_definable (M := M)
  unfold StackAgreement
  definability

theorem StackAgreement.trans {a b c : M} (h : StackAgreement a b) (k : StackAgreement b c) :
    StackAgreement a c :=
  ⟨h.1.trans k.1,fun i hi => (h.2 i hi).trans (k.2 i (h.1 ▸ hi))⟩

theorem StackAgreement.refl_of_left {a b : M} (h : StackAgreement a b) : StackAgreement a a :=
  ⟨rfl,fun i hi => LegacyAgreement.refl (h.2 i hi).1⟩

theorem StackAgreement.empty : StackAgreement (0 : M) 0 := by
  refine ⟨rfl,fun i hi => ?_⟩
  rw [len_nil] at hi
  exact (not_lt_of_ge (Arithmetic.zero_le i) hi).elim

theorem StackAgreement.cons {a b head next : M} (h : StackAgreement a b) (value : LegacyAgreement head next) :
    StackAgreement (head ∷ a) (next ∷ b) := by
  refine ⟨by simp [h.1],?_⟩
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i,rfl⟩
  · simpa only [nth_adjoin_zero] using value
  · rw [len_adjoin] at hi
    simpa only [nth_adjoin_succ] using h.2 i ((add_lt_add_iff_right 1).mp hi)

theorem StackAgreement.tail {a b : M} (h : StackAgreement a b) : StackAgreement (stackTail a) (stackTail b) := by
  rcases nil_or_adjoin a with rfl | ⟨x,a,rfl⟩
  · have zero : b = 0 := len_zero_iff_eq_nil.mp (h.1.symm.trans len_nil)
    subst b
    have empty : stackTail (0 : M) = 0 := by
      unfold stackTail
      rw [Arithmetic.sub_spec_of_le (Arithmetic.zero_le (1 : M)),Arithmetic.pi₂_zero]
    rw [empty]
    exact StackAgreement.empty
  · rcases nil_or_adjoin b with rfl | ⟨y,b,rfl⟩
    · have impossible := h.1
      rw [len_nil,len_adjoin] at impossible
      exact (lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)).ne' impossible |>.elim
    · simp only [stackTail_cons]
      refine ⟨?_,fun i hi => ?_⟩
      · simpa only [len_adjoin,add_left_inj] using h.1
      · have before : i+1 < len (x ∷ a) := by
          rw [len_adjoin]
          exact (add_lt_add_iff_right 1).mpr hi
        simpa only [nth_adjoin_succ] using h.2 _ before

theorem StackAgreement.pop {a b : M} (h : StackAgreement a b) (n : Nat) :
    StackAgreement (popStack n a) (popStack n b) := by
  induction n generalizing a b with
  | zero => exact h
  | succ n ih => exact ih h.tail

theorem StackAgreement.applySymbol {n : Nat} (f : FunctionSymbol n) {a b : M} (h : StackAgreement a b) :
    StackAgreement (legacyStackApply f a) (legacyStackApply f b) := by
  unfold legacyStackApply
  rw [← h.1]
  split
  · rename_i enough
    apply (h.pop n).cons
    apply LegacyAgreement.application f
    intro i
    have lt : (i.val : M) < (n : M) := by exact_mod_cast i.isLt
    exact h.2 _ (lt.trans_le enough)
  · exact h.cons (LegacyAgreement.refl (legacyConstant_valid .D))

theorem StackAgreement.applyToken (symbols : List (Σ n, FunctionSymbol n)) (token : M) {a b : M}
    (h : StackAgreement a b) : StackAgreement (legacySelect symbols token a) (legacySelect symbols token b) := by
  induction symbols with
  | nil => exact h.cons (LegacyAgreement.refl (legacyConstant_valid .D))
  | cons f rest ih =>
    simp only [legacySelect]
    split
    · exact h.applySymbol f.2
    · exact ih

theorem stackedFold_definable :
    𝚷ᴬ_[3].Definable (fun v : Fin 4 → M => StackAgreement (legacyFold (v 2) (v 1)) (legacyFold (v 3) (v 0))) := by
  letI foldDef := legacyFold_definable (M := M)
  have left : 𝚺ᴬ_[2].DefinableFunction (fun v : Fin 4 → M => legacyFold (v 2) (v 1)) :=
    Bounding.HierarchySymbol.DefinableFunction₂.comp (F := legacyFold) (.var 2) (.var 1)
  have right : 𝚺ᴬ_[2].DefinableFunction (fun v : Fin 4 → M => legacyFold (v 3) (v 0)) :=
    Bounding.HierarchySymbol.DefinableFunction₂.comp (F := legacyFold) (.var 3) (.var 0)
  have agreement : 𝚺ᴬ_[2]-Relation (StackAgreement (M := M)) := stackAgreement_definable.of_lt (by decide)
  exact (agreement.comp left right).of_lt (by decide)

theorem StackAgreement.fold (word : M) {a b : M} (h : StackAgreement a b) :
    StackAgreement (legacyFold word a) (legacyFold word b) := by
  let P := fun w : M => ∀ b a : M, StackAgreement a b → StackAgreement (legacyFold w a) (legacyFold w b)
  have impLeft : 𝚺ᴬ_[3].Definable (fun v : Fin 3 → M => StackAgreement (v 0) (v 1)) :=
    (stackAgreement_definable.of_lt (show (1 : Nat) < 3 by decide)).retraction (![0,1] : Fin 2 → Fin 3)
  have impRight := (stackedFold_definable (M := M)).retraction (![1,0,2,2] : Fin 4 → Fin 3)
  have prop : 𝚷ᴬ_[3]-Predicate P :=
    definableAllCons (definableAllCons (impLeft.imp (Γ := 𝚷) impRight))
  have all := modelVector_induction (P := P) prop
    (by intro b a related; simpa only [legacyFold_nil] using related)
    (fun head tail ih b a related => by
      change StackAgreement (modelFold (legacySelect legacySymbols) _ (head ∷ tail) a)
        (modelFold (legacySelect legacySymbols) _ (head ∷ tail) b)
      rw [modelFold_adjoin,modelFold_adjoin]
      exact (ih b a related).applyToken legacySymbols head)
  exact all word b a h

def LegacyWordAgreement (a b : M) : Prop :=
  ∀ s, StackAgreement s s → StackAgreement (legacyFold a s) (legacyFold b s)

theorem legacyWordAgreement_definable : 𝚷ᴬ_[3]-Relation (LegacyWordAgreement (M := M)) := by
  have assume : 𝚺ᴬ_[3].Definable (fun v : Fin 3 → M => StackAgreement (v 0) (v 0)) :=
    (stackAgreement_definable.of_lt (show (1 : Nat) < 3 by decide)).retraction (![0,0] : Fin 2 → Fin 3)
  have conclude := (stackedFold_definable (M := M)).retraction (![0,0,1,2] : Fin 4 → Fin 3)
  exact definableAllCons (assume.imp (Γ := 𝚷) conclude)

theorem LegacyWordAgreement.context {a b : M} (h : LegacyWordAgreement a b) (c : Context M) :
    LegacyWordAgreement (c.fill a) (c.fill b) := by
  intro s wellFormed
  have tail := wellFormed.fold c.after
  have replaced := h (legacyFold c.after s) tail
  simpa only [Context.fill,legacyFold_append] using replaced.fold c.before

theorem old_equation_agrees {row : PalomarI3380.Equation} (listed : row ∈ Manifest.final)
    (args : Fin 3 → GroundTerm M) :
    LegacyWordAgreement (termTokens (groundAlgebra.eval args row.1).val)
      (termTokens (groundAlgebra.eval args row.2).val) := by
  intro s wellFormed
  have left := pushesLegacy (groundAlgebra.eval args row.1)
  have right := pushesLegacy (groundAlgebra.eval args row.2)
  rw [left.2,right.2]
  apply wellFormed.cons
  apply legacyAgreement_iff.mpr
  refine ⟨left.1,right.1,?_⟩
  rw [legacyEval_term,legacyEval_term]
  exact (legacyModel.models_final_of_preceding legacyModel_models) row listed _

theorem old_rewrite_agrees {x y : M} (step : RewriteStep x y) : LegacyWordAgreement x y := by
  obtain ⟨row,listed,raw,typed,ctx,side⟩ := step
  obtain ⟨args,rfl⟩ := termArguments (n := 3) typed
  simp only [instantiate_eval] at side
  have both := (old_equation_agrees listed args).context ctx
  rcases side with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact both
  · intro s typed
    have h := both s typed
    refine ⟨h.1.symm,fun i hi => ?_⟩
    obtain ⟨ha,hb,eq,bit⟩ := h.2 i (h.1.symm ▸ hi)
    exact ⟨hb,ha,eq.symm,bit.symm⟩

theorem old_convertible_agrees {x y : M} (replay : Convertible x y) : LegacyWordAgreement x y := by
  obtain ⟨count,trace,_,first,last,edges⟩ := replay
  let P := fun i : M => i ≤ count → LegacyWordAgreement x trace.[i]
  have condition : 𝚺ᴬ_[3]-Predicate (fun i : M => i ≤ count) := by definability
  have get : 𝚺ᴬ_[3].DefinableFunction (fun v : Fin 1 → M => trace.[v 0]) := by definability
  have eq := (legacyWordAgreement_definable (M := M)).comp
    (Bounding.HierarchySymbol.DefinableFunction.const x) get
  have prop : 𝚷ᴬ_[3]-Predicate P := condition.imp (Γ := 𝚷) eq
  have carried := InductionOnHierarchy.succ_induction_sigma 𝚷 3 prop
    (by intro _; rw [first]; exact fun s shape => shape.fold x)
    (fun i ih bound s shape => by
      have earlier := succ_le_iff_lt.mp bound
      exact (ih (le_of_lt earlier) s shape).trans (old_rewrite_agrees (edges i earlier) s shape))
  exact last ▸ carried count le_rfl

end PalomarI3334.SearchProgram
