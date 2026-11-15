module
public import ModelPhysicalOrientation
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def WriteScanRight (q:Nat) (b w:Bool) (n:M) : Prop := ∀l r initial hist:M,
 runHistory initial hist → modelListHead hist=stateCode ⟨(q:M),l,bitRun n (bitValue b) r⟩ →
 ∃out,runHistory initial out ∧ modelListHead out=stateCode ⟨(q:M),bitRun n (bitValue w) l,r⟩
def writeScanRightFormulaOf (run:ArithmeticSemisentence 2) (runs:𝚺ᴬ₁.Semisentence 4)
 (q:Nat) (b w:Bool) : ArithmeticSemiformula Nat 1 :=
 let bit:=boolNat b
 let outbit:=boolNat w
 “n. ∀l, ∀r, ∀initial, ∀hist, ∀right, ∀left, ∀before, ∀after,
 !runs right n ↑bit r → !runs left n ↑outbit l →
 !stateGraph before ↑q l right → !stateGraph after ↑q left r →
 !run initial hist → !listHeadGraph before hist →
 ∃out, !run initial out ∧ !listHeadGraph after out”
lemma writeScanRightFormula_eval (ρ:Nat→M) (q:Nat) (b w:Bool) (n:M) :
 (writeScanRightFormulaOf physicalRunFormula bitRunGraph q b w).Eval ![n] ρ ↔ WriteScanRight q b w n := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [writeScanRightFormulaOf,WriteScanRight,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
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
lemma physical_write_scan_right (q:Nat) (b w:Bool)
 (row:M209.literal q b=some (w,true,q)) : ∀n:M,WriteScanRight q b w n := by
 haveI : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
  models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔)
 refine InductionScheme.succ_induction (C:=Set.univ) (P:=WriteScanRight q b w) ?_ ?_ ?_
 · exact ⟨(fun _=>0),writeScanRightFormulaOf physicalRunFormula bitRunGraph q b w,by trivial,
    fun n=>(writeScanRightFormula_eval (fun _=>0) q b w n).symm⟩
 · intro l r initial hist hh he
   refine ⟨hist,hh,?_⟩
   simpa only [bitRun_zero] using he
 · intro n ih l r initial hist hh he
   let next:State M := ⟨(q:M),bitValue w+2*l,bitRun n (bitValue b) r⟩
   have hm:move b w true (q:M) ⟨(q:M),l,bitRun (n+1) (bitValue b) r⟩ next :=
    ⟨bitRun n (bitValue b) r,bitRun_succ n _ _,rfl,rfl,rfl⟩
   have hs:codedStep (modelListHead hist) (stateCode next) := by
    rw [he]
    exact ⟨_,next,rfl,rfl,q,literal_row_bound _ _ _ _ _ row,rfl,b,w,true,q,row,hm⟩
   have hr:=runHistory_extend hh hs
   obtain ⟨out,ho,hend⟩:=ih (bitValue w+2*l) r initial
    (modelListCons (stateCode next) hist) hr (modelListHead_cons _ _)
   refine ⟨out,ho,?_⟩
   simpa only [bitRun_commute] using hend
lemma named_write_scan_right (q:Nat) (b w:Bool) (n l r:M)
 (row:M209.renamed q b=some (w,true,q)) :
 Reaches (namedState q l (bitRun n (bitValue b) r))
 (namedState q (bitRun n (bitValue w) l) r) :=
 physical_write_scan_right (M209.forward q) b w (literal_of_renamed_row row) n l r
end ZF209.BinaryTape
