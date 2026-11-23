module
public import I3_334.Calibration.ModelTrialCoverage
public import I3_334.Calibration.ModelEntry
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (definableAllCons)
open PalomarI3380.Arithmetic (Chain)
open ArithmeticMachine.SourceWords
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- A stream starts at a reset or a paid pending word. Scratch belongs
to the machine state and ranges over all possible previous trials. -/
def WorksAt (word input : M) : Prop :=
  (∀ i t : M, CodedTermination (schedulerCode i (input+1) word t)) ∧
    (word=4 → ∀ g t : M, CodedTermination (schedulerCode input 0 g t))

def HasTrial (word : M) : Prop :=
  ∃ input > 0, WorksAt word input

theorem worksAt_definable : 𝚷ᴬ_[2]-Relation (WorksAt (M := M)) := by
  let code : 𝚺ᴬ_[2]-Function₄ (schedulerCode (M := M)) :=
    (schedulerCode_definable (M := M)).of_lt (by decide)
  have terminates : 𝚷ᴬ_[2]-Predicate (CodedTermination (M := M)) :=
    (codedTermination_definable (M := M)).of_lt (by decide)
  have pending : 𝚷ᴬ_[2].Definable (fun v : Fin 4 → M =>
      CodedTermination (schedulerCode (v 1) (v 3+1) (v 2) (v 0))) := by
    refine terminates.comp (Bounding.HierarchySymbol.DefinableFunction₄.comp
      (F := schedulerCode) (.var 1) ?_ (.var 2) (.var 0))
    definability
  have reset : 𝚷ᴬ_[2].Definable (fun v : Fin 4 → M =>
      CodedTermination (schedulerCode (v 3) 0 (v 1) (v 0))) :=
    terminates.comp (Bounding.HierarchySymbol.DefinableFunction₄.comp (F := schedulerCode)
      (.var 3) (.const 0) (.var 1) (.var 0))
  have literal : 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => v 0=4) := by definability
  exact (definableAllCons (definableAllCons pending)).and
    (literal.imp (Γ := 𝚷) (definableAllCons (definableAllCons reset)))

theorem hasTrial_definable : 𝚺ᴬ_[3]-Predicate (HasTrial (M := M)) := by
  have works : 𝚺ᴬ_[3]-Relation (WorksAt (M := M)) :=
    (worksAt_definable (M := M)).of_lt (by decide)
  unfold HasTrial
  definability

theorem modelRewrite_hasTrial {x y : M} (step : ModelRewrite x y)
    (downstream : emitVector y 0=1 ∨ HasTrial (emitVector y 0)) :
    HasTrial (emitVector x 0) := by
  have suitable :
      ∃ tail : M, emitVector y 0 ≠ 1 → ∀ i t, CodedTermination (schedulerCode i tail (emitVector y 0) t) := by
    rcases downstream with endNow | ⟨next,_,replay⟩
    · exact ⟨0,fun nonfinal => (nonfinal endNow).elim⟩
    · exact ⟨next+1,fun _ => replay.1⟩
  obtain ⟨tail,carry⟩ := suitable
  obtain ⟨input,positive,trial⟩ := modelRewrite_coded_trial step tail
  have use (s : Scheduler M) (ready : s.begin.pending=input) (value : s.begin.incumbent=emitVector x 0) :
      CodedTermination s.store.code := by
    obtain ⟨scratchWord,run⟩ := trial s ready value
    by_cases endNow : emitVector y 0=1
    · exact .of_halt (by simpa only [trialFlow,endNow,↓reduceIte] using run)
    · exact (carry endNow s.begin.index scratchWord).prepend
        (by simpa only [schedulerCode,Scheduler.finish,trialFlow,endNow,↓reduceIte] using run)
  refine ⟨input,positive,?_,?_⟩
  · intro index scratchWord
    let s : Scheduler M := ⟨index,input+1,emitVector x 0,scratchWord⟩
    have nonzero : input+1≠0 := (lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one input)).ne'
    exact use s (by simp [s,Scheduler.begin,nonzero]) (by simp [s,Scheduler.begin,nonzero])
  · intro isStart current scratchWord
    let s : Scheduler M := ⟨input,0,current,scratchWord⟩
    exact use s (by simp [s,Scheduler.begin]) (by simp [s,Scheduler.begin,isStart])

theorem modelChain_first_hasTrial {n x y : M} (chain : Chain ModelRewrite n x y) (positive : 0 < n)
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
    apply modelRewrite_hasTrial (steps _ previous)
    exact Or.inl (by rw [ends,last,target])) (fun k ih fit => by
      have before : k < n := (lt_add_one k).trans fit
      have less : n-1-(k+1) < n := by
        exact lt_of_le_of_lt (Arithmetic.sub_le_self ..) previous
      apply modelRewrite_hasTrial (steps _ less)
      exact Or.inr (by rw [adjacent fit]; exact ih before))
  have atFirst := all (n-1) previous
  simpa only [P,Arithmetic.sub_self,first] using atFirst

theorem coded_halts_of_modelDerives {a b : M}
    (start : emitVector a 0 = 4) (last : emitVector b 0 = 1) (derivation : ModelDerives a b) :
    (ArithmeticMachine.haltsDef 334 packedLiteral).val.Evalb (![] : Fin 0 → M) := by
  obtain ⟨n,chain⟩ := derivation
  have positive : 0 < n := by
    by_contra notpos
    have zero : n=0 := nonpos_iff_eq_zero.mp (le_of_not_gt notpos)
    obtain ⟨trace,_,begins,ends,_⟩ := chain
    rw [zero] at ends
    have clash : (4 : M) = 1 := start.symm.trans ((congrArg (emitVector · 0) (begins.symm.trans ends)).trans last)
    exact (by exact_mod_cast (show (4 : Nat) ≠ 1 by decide) : (4 : M) ≠ 1) clash
  obtain ⟨target,size,ready⟩ := modelChain_first_hasTrial chain positive last
  have entry : entryStore (M := M) = (Scheduler.mk (1 : M) 0 0 0).store := by
    apply Source.store_ext <;> simp [entryStore,Scheduler.store,Store.set,np,pl,fr,tmp]
  apply CodedTermination.literal_halts
  rw [entry]
  exact coded_seek target (ready.2 start) ⟨1,0,0,0⟩ (pos_iff_one_le.mp size) (Arithmetic.zero_le _)

end PalomarI3334.SearchProgram
