module
public import ModelBitRuns
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def ScanRight (q:Nat) (b:Bool) (n:M) : Prop := ∀l r initial hist:M,
 runHistory initial hist → modelListHead hist=stateCode ⟨(q:M),l,bitRun n (bitValue b) r⟩ →
 ∃out,runHistory initial out ∧ modelListHead out=stateCode ⟨(q:M),bitRun n (bitValue b) l,r⟩
def scanRightFormulaOf (run:ArithmeticSemisentence 2) (runs:𝚺ᴬ₁.Semisentence 4)
 (q:Nat) (b:Bool) : ArithmeticSemiformula Nat 1 :=
 let bit:=boolNat b
 “n. ∀l, ∀r, ∀initial, ∀hist, ∀right, ∀left, ∀before, ∀after,
 !runs right n ↑bit r → !runs left n ↑bit l →
 !stateGraph before ↑q l right → !stateGraph after ↑q left r →
 !run initial hist → !listHeadGraph before hist →
 ∃out, !run initial out ∧ !listHeadGraph after out”
lemma scanRightFormula_eval (ρ:Nat→M) (q:Nat) (b:Bool) (n:M) :
 (scanRightFormulaOf physicalRunFormula bitRunGraph q b).Eval ![n] ρ ↔ ScanRight q b n := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [scanRightFormulaOf,ScanRight,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Empty.eq_elim,hv,bitRun_defined.iff,stateGraph_eval,physicalRunFormula_eval,
 ruleHead_defined.iff,numeral_eq_natCast,boolNat_cast,eq_comm]
 constructor
 · intro h l r initial hist hh he
   obtain ⟨out,ho,hend⟩:=h l r initial hist _ _ _ _ rfl rfl rfl rfl hh he.symm
   exact ⟨out,ho,hend.symm⟩
 · intro h l r initial hist right left before after hr hl hb ha hh he
   rw [hr] at hb
   rw [hl] at ha
   obtain ⟨out,ho,hend⟩:=h l r initial hist hh (he.symm.trans hb)
   exact ⟨out,ho,ha.trans hend.symm⟩
/-- Actual literal self-loop scanned for an arbitrary internal model length.
The supplied prefix remains rooted at the identical original start code. -/
lemma physical_scan_right (q:Nat) (b:Bool)
 (row:M207.literal q b=some (b,true,q)) : ∀n:M,ScanRight q b n := by
 haveI : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
  models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔)
 refine InductionScheme.succ_induction (C:=Set.univ) (P:=ScanRight q b) ?_ ?_ ?_
 · exact ⟨(fun _=>0),scanRightFormulaOf physicalRunFormula bitRunGraph q b,by trivial,
    fun n=>(scanRightFormula_eval (fun _=>0) q b n).symm⟩
 · intro l r initial hist hh he
   refine ⟨hist,hh,?_⟩
   simpa only [bitRun_zero] using he
 · intro n ih l r initial hist hh he
   let next:State M := ⟨(q:M),bitValue b+2*l,bitRun n (bitValue b) r⟩
   have hm:move b b true (q:M) ⟨(q:M),l,bitRun (n+1) (bitValue b) r⟩ next :=
    ⟨bitRun n (bitValue b) r,bitRun_succ n _ _,rfl,rfl,rfl⟩
   have hs:codedStep (modelListHead hist) (stateCode next) := by
    rw [he]
    exact ⟨_,next,rfl,rfl,q,literal_row_bound _ _ _ _ _ row,rfl,b,b,true,q,row,hm⟩
   have hr:=runHistory_extend hh hs
   obtain ⟨out,ho,hend⟩:=ih (bitValue b+2*l) r initial
    (modelListCons (stateCode next) hist) hr (modelListHead_cons _ _)
   refine ⟨out,ho,?_⟩
   simpa only [bitRun_commute] using hend
end ZF207.BinaryTape
