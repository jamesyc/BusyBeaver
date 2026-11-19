module
public import ModelBitRuns
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- The cell initially under the head is b; n further b cells lie immediately left.
After n left moves the right numeral contains the original cell and those n cells. -/
def ScanLeft (q:Nat) (b:Bool) (n:M) : Prop := ∀l r initial hist:M,
 runHistory initial hist →
 modelListHead hist=stateCode ⟨(q:M),bitRun n (bitValue b) l,bitValue b+2*r⟩ →
 ∃out,runHistory initial out ∧
 modelListHead out=stateCode ⟨(q:M),l,bitRun n (bitValue b) (bitValue b+2*r)⟩
def scanLeftFormulaOf (run:ArithmeticSemisentence 2) (runs:𝚺ᴬ₁.Semisentence 4)
 (q:Nat) (b:Bool) : ArithmeticSemiformula Nat 1 :=
 let bit:=boolNat b
 “n. ∀l, ∀r, ∀initial, ∀hist, ∀left, ∀right, ∀before, ∀after,
 !runs left n ↑bit l → !runs right n ↑bit (↑bit+2*r) →
 !stateGraph before ↑q left (↑bit+2*r) → !stateGraph after ↑q l right →
 !run initial hist → !listHeadGraph before hist →
 ∃out, !run initial out ∧ !listHeadGraph after out”
lemma scanLeftFormula_eval (ρ:Nat→M) (q:Nat) (b:Bool) (n:M) :
 (scanLeftFormulaOf physicalRunFormula bitRunGraph q b).Eval ![n] ρ ↔ ScanLeft q b n := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [scanLeftFormulaOf,ScanLeft,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Empty.eq_elim,hv,bitRun_defined.iff,stateGraph_eval,physicalRunFormula_eval,
 ruleHead_defined.iff,numeral_eq_natCast,boolNat_cast,eq_comm]
 constructor
 · intro h l r initial hist hh he
   obtain ⟨out,ho,hend⟩:=h l r initial hist _ _ _ _ rfl rfl rfl rfl hh he.symm
   exact ⟨out,ho,hend.symm⟩
 · intro h l r initial hist left right before after hl hr hb ha hh he
   rw [hl] at hb
   rw [hr] at ha
   obtain ⟨out,ho,hend⟩:=h l r initial hist hh (he.symm.trans hb)
   exact ⟨out,ho,ha.trans hend.symm⟩
/-- Actual literal left self-loop for an arbitrary internal model length, retaining
any supplied rooted prefix and its identical initial state. -/
lemma physical_scan_left (q:Nat) (b:Bool)
 (row:M207.literal q b=some (b,false,q)) : ∀n:M,ScanLeft q b n := by
 haveI : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
  models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔)
 refine InductionScheme.succ_induction (C:=Set.univ) (P:=ScanLeft q b) ?_ ?_ ?_
 · exact ⟨(fun _=>0),scanLeftFormulaOf physicalRunFormula bitRunGraph q b,by trivial,
    fun n=>(scanLeftFormula_eval (fun _=>0) q b n).symm⟩
 · intro l r initial hist hh he
   refine ⟨hist,hh,?_⟩
   simpa only [bitRun_zero] using he
 · intro n ih l r initial hist hh he
   let next:State M := ⟨(q:M),bitRun n (bitValue b) l,bitValue b+2*(bitValue b+2*r)⟩
   have hm:move b b false (q:M)
     ⟨(q:M),bitRun (n+1) (bitValue b) l,bitValue b+2*r⟩ next := by
    refine ⟨r,rfl,rfl,bitRun n (bitValue b) l,bitValue b,bitValue_cases b,
     bitRun_succ n _ _,rfl,?_⟩
    have h4:(2:M)*2=4 := by norm_num
    simp only [next,mul_add,←mul_assoc,h4,add_assoc]
   have hs:codedStep (modelListHead hist) (stateCode next) := by
    rw [he]
    exact ⟨_,next,rfl,rfl,q,literal_row_bound _ _ _ _ _ row,rfl,b,b,false,q,row,hm⟩
   have hr:=runHistory_extend hh hs
   obtain ⟨out,ho,hend⟩:=ih l (bitValue b+2*r) initial
    (modelListCons (stateCode next) hist) hr (modelListHead_cons _ _)
   refine ⟨out,ho,?_⟩
   simpa only [bitRun_commute] using hend
end ZF207.BinaryTape
