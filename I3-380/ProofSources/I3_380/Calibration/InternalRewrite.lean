module
public import I3_380.Calibration.CodedRewriteTrial
public import I3_380.Calibration.GroundQuotient
public import I3_380.Search.Arithmetic.SchedulerSearch
public import I3_380.Search.Arithmetic.LoopEntry
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PalomarI3380.Compiler PalomarI3380.Compiler.Source
open ArithmeticMachine.SourceWords (emitVector appendVector_length)
open ArithmeticMachine.SourceCantor (pairValue pairValue_bounds)
open PalomarI3380.Arithmetic (Chain)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem args_from_code {raw : M} (typed : IsSemitermVec FilterLanguage 3 0 raw) :
    ∃ args : Fin 3 → GroundTerm M, raw = matrixToVec (fun i => (args i).val) := by
  have castThree : ((3 : Nat) : M) = 3 := by simp
  let args (i : Fin 3) : GroundTerm M := ⟨raw.[(i.val : M)],by
    simpa using typed.nth (show (i.val : M) < 3 from by rw [← castThree]; exact_mod_cast i.isLt)⟩
  refine ⟨args,nth_ext' 3 (typed.lh) (by simp [one_add_one_eq_two,two_add_one_eq_three]) ?_⟩
  intro i bound
  have small : i ≤ 2 := lt_succ_iff_le.mp (by rwa [two_add_one_eq_three])
  rcases le_two_iff_eq_zero_or_one_or_two.mp small with rfl | rfl | rfl
  · simpa [args] using (matrixToVec_nth (fun j => (args j).val) (0 : Fin 3)).symm
  · simpa [args] using (matrixToVec_nth (fun j => (args j).val) (1 : Fin 3)).symm
  · simpa [args] using (matrixToVec_nth (fun j => (args j).val) (2 : Fin 3)).symm

theorem Context.field_positive (ctx : Context M) (t : GroundTerm M) :
    0 < emitVector (ctx.fill (termTokens t.val)) 0 := by
  have nonempty : termTokens t.val ≠ 0 := fun h => by
    have positive := termWord_nonempty t
    simpa [termWord,h] using positive
  apply ArithmeticMachine.SourceWords.emitVector_nonempty
  intro empty
  have positive : 0 < len (termTokens t.val) := by
    exact lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm (fun h => nonempty (len_zero_iff_eq_nil.mp h)))
  have fits : len (termTokens t.val) ≤ len (ctx.fill (termTokens t.val)) := by
    simp only [Context.fill,appendVector_length]
    calc
      len (termTokens t.val) ≤ len (termTokens t.val)+len ctx.after :=
        le_add_of_nonneg_right (Arithmetic.zero_le _)
      _ ≤ len ctx.before+(len (termTokens t.val)+len ctx.after) :=
        le_add_of_nonneg_left (Arithmetic.zero_le _)
  simpa [empty] using positive.trans_le fits

theorem RewriteStep.coded_trial {x y : M} (step : RewriteStep x y) (tail : M) :
    ∃ input : M, 0 < input ∧ ∀ s : SchedulerState M,
      s.begin.pending=input → s.begin.current=emitVector x 0 →
      main.Runs (if emitVector y 0=1 then .halt else .normal) s.store.code
        (schedulerCode s.begin.nextWord tail (if emitVector y 0=1 then 0 else emitVector y 0)) := by
  obtain ⟨row,member,raw,valid,ctx,orientation⟩ := step
  obtain ⟨args,rfl⟩ := args_from_code valid
  rw [instantiate_eval,instantiate_eval] at orientation
  let lhs := termTokens (groundAlgebra.eval args row.1).val
  let rhs := termTokens (groundAlgebra.eval args row.2).val
  obtain ⟨rev,left,right⟩ : ∃ rev : Bool,
      x=ctx.fill (if rev then rhs else lhs) ∧ y=ctx.fill (if rev then lhs else rhs) := by
    rcases orientation with ⟨first,second⟩ | ⟨first,second⟩
    · exact ⟨false,first,second⟩
    · exact ⟨true,first,second⟩
  obtain ⟨fields,trial⟩ := coded_rewrite_instance member args ctx rev
  let c : TrialInput M :=
    ⟨emitVector y 0,len ctx.before,if rev then 1 else 0,termDictionary args,modelFields fields tail⟩
  have positive : 0 < emitVector y 0 := by
    rw [right]
    cases rev
    · exact ctx.field_positive (groundAlgebra.eval args row.2)
    · exact ctx.field_positive (groundAlgebra.eval args row.1)
  refine ⟨c.modelEncode,positive.trans_le (pairValue_bounds _ _).1,fun s word value => ?_⟩
  have word' : s.begin.pending = (TrialInput.mk (emitVector y 0) (len ctx.before) (if rev then 1 else 0)
      (termDictionary args) (modelFields fields tail)).modelEncode := word
  have value' := value
  rw [right] at word'
  rw [left] at value'
  have exec := trial s tail word' value'
  rw [right]
  exact exec

/-- The same stream works both at a reset and as a pending suffix. -/
def WorksAt (word input : M) : Prop :=
  (∀ i : M, CodedTermination (schedulerCode i (input+1) word)) ∧
    (word=4 → ∀ g : M, CodedTermination (schedulerCode input 0 g))

def HasTrial (word : M) : Prop :=
  ∃ input > 0, WorksAt word input

theorem worksAt_definable : 𝚷ᴬ_[2]-Relation (WorksAt (M := M)) := by
  letI code : 𝚺ᴬ_[2]-Function₃ (schedulerCode (M := M)) :=
    (schedulerCode_definable (M := M)).of_lt (by decide)
  have terminates : 𝚷ᴬ_[2]-Predicate (CodedTermination (M := M)) :=
    (codedTermination_definable (M := M)).of_lt (by decide)
  have cont : 𝚷ᴬ_[2].Definable (fun v : Fin 3 → M => CodedTermination (schedulerCode (v 0) (v 2+1) (v 1))) := by
    refine terminates.comp (Bounding.HierarchySymbol.DefinableFunction₃.comp (.var 0) ?_ (.var 1))
    definability
  have reset : 𝚷ᴬ_[2].Definable (fun v : Fin 3 → M => CodedTermination (schedulerCode (v 2) 0 (v 0))) :=
    terminates.comp (Bounding.HierarchySymbol.DefinableFunction₃.comp (.var 2) (.const 0) (.var 0))
  have literal : 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => v 0=4) := by definability
  exact (definableAllCons cont).and (literal.imp (Γ := 𝚷) (definableAllCons reset))

theorem hasTrial_definable : 𝚺ᴬ_[3]-Predicate (HasTrial (M := M)) := by
  have works : 𝚺ᴬ_[3]-Relation (WorksAt (M := M)) :=
    (worksAt_definable (M := M)).of_lt (by decide)
  unfold HasTrial
  definability

theorem WorksAt.apply_of_begin {word input : M} (good : WorksAt word input)
    (s : SchedulerState M) (stream : s.begin.pending = input) (term : s.begin.current = word) :
    CodedTermination s.store.code := by
  by_cases empty : s.pending=0
  · have index : s.nextWord=input := by simpa [SchedulerState.begin,empty] using stream
    have start : word=4 := by simpa [SchedulerState.begin,empty] using term.symm
    simpa [schedulerCode,← index,← empty] using good.2 start s.current
  · have rest : s.pending-1=input := by simpa [SchedulerState.begin,empty] using stream
    have currently : s.current=word := by simpa [SchedulerState.begin,empty] using term
    have pending : s.pending=input+1 := by
      have positive : 0 < s.pending := lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm empty)
      exact (tsub_add_cancel_of_le (pos_iff_one_le.mp positive)).symm.trans (congrArg (· + 1) rest)
    simpa [schedulerCode,← pending,← currently] using good.1 s.nextWord

theorem RewriteStep.hasTrial {x y : M} (step : RewriteStep x y)
    (downstream : emitVector y 0=1 ∨ HasTrial (emitVector y 0)) :
    HasTrial (emitVector x 0) := by
  have suitable :
      ∃ tail : M, emitVector y 0 ≠ 1 → ∀ i, CodedTermination (schedulerCode i tail (emitVector y 0)) := by
    rcases downstream with endNow | ⟨next,_,replay⟩
    · exact ⟨0,fun nonfinal => (nonfinal endNow).elim⟩
    · exact ⟨next+1,fun _ => replay.1⟩
  obtain ⟨tail,carry⟩ := suitable
  obtain ⟨input,positive,trial⟩ := step.coded_trial tail
  have use (s : SchedulerState M) (ready : s.begin.pending=input) (value : s.begin.current=emitVector x 0) :
      CodedTermination s.store.code := by
    have run := trial s ready value
    by_cases endNow : emitVector y 0=1
    · exact .of_halt (by simpa only [endNow,↓reduceIte] using run)
    · exact (carry endNow s.begin.nextWord).prepend (by simpa only [endNow,↓reduceIte] using run)
  refine ⟨input,positive,?_,?_⟩
  · intro index
    let s : SchedulerState M := ⟨index,input+1,emitVector x 0⟩
    have nonzero : input+1≠0 := (lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one input)).ne'
    exact use s (by simp [s,SchedulerState.begin,nonzero]) (by simp [s,SchedulerState.begin,nonzero])
  · intro isStart current
    let s : SchedulerState M := ⟨input,0,current⟩
    exact use s (by simp [s,SchedulerState.begin]) (by simp [s,SchedulerState.begin,isStart])

theorem Chain.first_hasTrial {n x y : M} (chain : Chain RewriteStep n x y) (positive : 0 < n)
    (target : emitVector y 0=1) : HasTrial (emitVector x 0) := by
  obtain ⟨trace,_,first,last,steps⟩ := chain
  let P := fun k : M => k < n → HasTrial (emitVector trace.[n-1-k] 0)
  have existsTrial := hasTrial_definable (M := M)
  have word : 𝚺ᴬ₁-Function₁ (fun k : M => emitVector trace.[n-1-k] 0) := by definability
  have arg : 𝚺ᴬ_[3].DefinableFunction (fun v : Fin 1 → M => emitVector trace.[n-1-v 0] 0) :=
    word.of_lt (by decide)
  have before : 𝚷ᴬ_[3]-Predicate (fun k : M => k<n) := by definability
  have definition : 𝚺ᴬ_[3]-Predicate P := before.imp (Γ := 𝚺) (existsTrial.comp arg)
  have adjacent {k : M} (bound : k+1 < n) : n-1-(k+1)+1=n-1-k := by
    rw [← Arithmetic.sub_sub]
    have enough : 1 ≤ n-1-k := by
      apply pos_iff_one_le.mp
      apply Arithmetic.pos_sub_iff_lt.mpr
      rw [← tsub_add_cancel_of_le (pos_iff_one_le.mp positive)] at bound
      exact (add_lt_add_iff_right 1).mp bound
    exact tsub_add_cancel_of_le enough
  have ends : n-1+1=n := tsub_add_cancel_of_le (pos_iff_one_le.mp positive)
  have previous : n-1<n := by
    have before := lt_add_one (n-1)
    rwa [ends] at before
  have all := InductionOnHierarchy.succ_induction_sigma 𝚺 3 definition (by
    intro _
    simp only [Arithmetic.sub_zero]
    apply (steps _ previous).hasTrial
    exact Or.inl (by rw [ends,last,target])) (fun k ih fit => by
      have before : k < n := (lt_add_one k).trans fit
      have less : n-1-(k+1) < n := by
        exact lt_of_le_of_lt (Arithmetic.sub_le_self ..) previous
      apply (steps _ less).hasTrial
      exact Or.inr (by rw [adjacent fit]; exact ih before))
  have atFirst := all (n-1) previous
  simpa only [P,Arithmetic.sub_self,first] using atFirst

theorem triangle_one : ArithmeticMachine.SourceCantor.triangleValue (1 : M)=1 := by
  simpa only [zero_add,ArithmeticMachine.SourceCantor.triangle_zero] using
    ArithmeticMachine.SourceCantor.triangle_succ (0 : M)

theorem triangle_two : ArithmeticMachine.SourceCantor.triangleValue (2 : M)=3 := by
  rw [← one_add_one_eq_two,ArithmeticMachine.SourceCantor.triangle_succ,triangle_one,
    one_add_one_eq_two,two_add_one_eq_three]

theorem constD_word : termWord ((groundAlgebra (M := M)).constant .D).val=4 := by
  change emitVector (termTokens (application (.constant .D) ![]).val) 0 = _
  rw [application_tokens]
  have code : (⌜(show FilterLanguage.Func 0 from FunctionSymbol.constant .D)⌝ : M) = 1 := by
    change ((1 : Nat) : M) = 1
    exact Nat.cast_one
  simp [code,ArithmeticMachine.SourceWords.cons,pairValue,
    triangle_one,triangle_two,one_add_one_eq_two,three_add_one_eq_four]

theorem constJ_word : termWord ((groundAlgebra (M := M)).constant .J).val=1 := by
  change emitVector (termTokens (application (.constant .J) ![]).val) 0 = _
  rw [application_tokens]
  have code : (⌜(show FilterLanguage.Func 0 from FunctionSymbol.constant .J)⌝ : M) = 0 := rfl
  simp [code,ArithmeticMachine.SourceWords.cons,pairValue,triangle_one]

theorem model_halts_of_distinction_failure
    (collapsed : (quotientAlgebra (M := M)).withStages.constant .D =
      (quotientAlgebra (M := M)).withStages.constant .J) :
    (ArithmeticMachine.haltsDef 380 packedLiteral).val.Evalb (![] : Fin 0 → M) := by
  have converts : Convertible
      (termTokens ((groundAlgebra (M := M)).constant .D).val)
      (termTokens ((groundAlgebra (M := M)).constant .J).val) := Quotient.exact collapsed
  obtain ⟨n,chain⟩ := converts
  have positive : 0 < n := by
    by_contra notpos
    have zero : n=0 := nonpos_iff_eq_zero.mp (le_of_not_gt notpos)
    obtain ⟨trace,_,left,right,_⟩ := chain
    rw [zero] at right
    have same := left.symm.trans right
    have clash : (4 : M)=1 := constD_word.symm.trans ((congrArg (emitVector · 0) same).trans constJ_word)
    have nonzero : (1 : M) < 4 := by
      calc
        (1 : M) < 1+1 := lt_add_one _
        _ < (1+1)+1 := lt_add_one _
        _ < 4 := by
          rw [one_add_one_eq_two,two_add_one_eq_three,← three_add_one_eq_four]
          exact lt_add_one _
    exact nonzero.ne clash.symm
  have preferred := Chain.first_hasTrial chain positive constJ_word
  obtain ⟨target,positive,ready⟩ := preferred
  have start : entryStore (M := M) = (SchedulerState.mk (1 : M) 0 0).store := by
    apply store_ext <;> simp [entryStore,SchedulerState.store,emptyStore,Store.set,np,pl,goal]
  apply CodedTermination.literal_halts
  rw [start]
  exact coded_seek target (ready.2 constD_word) ⟨1,0,0⟩ (pos_iff_one_le.mp positive)
    (Arithmetic.zero_le _)

end PalomarI3380.Calibration.TermWords
