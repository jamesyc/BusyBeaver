module
public import ModelPhysicalSpareReturn
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def WriteScanLeft (q:Nat) (b w:Bool) (n:M) : Prop := ∀l r initial hist:M,
 runHistory initial hist → modelListHead hist=stateCode (namedLeft q (bitRun n (bitValue b) l) r) →
 ∃out,runHistory initial out ∧ modelListHead out=stateCode (namedLeft q l (bitRun n (bitValue w) r))
def writeScanLeftFormulaOf (run:ArithmeticSemisentence 2) (runs:𝚺ᴬ₁.Semisentence 4)
 (q:Nat) (b w:Bool) : ArithmeticSemiformula Nat 1 :=
 let left:=leftStateGraph q
 let ib:=boolNat b
 let ob:=boolNat w
 “n. ∀l, ∀r, ∀initial, ∀hist, ∀right, ∀ls, ∀before, ∀after,
 !runs right n ↑ob r → !runs ls n ↑ib l → !left before ls r → !left after l right →
 !run initial hist → !listHeadGraph before hist → ∃out,!run initial out ∧ !listHeadGraph after out”
lemma writeScanLeftFormula_eval (ρ:Nat→M) (q:Nat) (b w:Bool) (n:M) :
 (writeScanLeftFormulaOf physicalRunFormula bitRunGraph q b w).Eval ![n] ρ ↔ WriteScanLeft q b w n := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [writeScanLeftFormulaOf,WriteScanLeft,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Empty.eq_elim,hv,bitRun_defined.iff,leftStateGraph_eval,physicalRunFormula_eval,
 ruleHead_defined.iff,numeral_eq_natCast,boolNat_cast]
 constructor
 · intro h l r initial hist hh he
   obtain ⟨out,ho,hend⟩:=h l r initial hist _ _ _ _ rfl rfl rfl rfl hh he.symm
   exact ⟨out,ho,hend.symm⟩
 · intro h l r initial hist right ls before after hr hl hb ha hh he
   rw [hr] at ha; rw [hl] at hb
   obtain ⟨out,ho,hend⟩:=h l r initial hist hh (he.symm.trans hb)
   exact ⟨out,ho,ha.trans hend.symm⟩
lemma named_write_scan_left (q:Nat) (b w:Bool)
 (row:M209.renamed q b=some (w,false,q)) (n l r:M) :
 Reaches (namedLeft q (bitRun n (bitValue b) l) r)
 (namedLeft q l (bitRun n (bitValue w) r)) := by
 haveI : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔)
 have hall:∀n:M,WriteScanLeft q b w n := by
  refine InductionScheme.succ_induction (C:=Set.univ) (P:=WriteScanLeft q b w) ?_ ?_ ?_
  · exact ⟨(fun _=>0),writeScanLeftFormulaOf physicalRunFormula bitRunGraph q b w,by trivial,
     fun n=>(writeScanLeftFormula_eval (fun _=>0) q b w n).symm⟩
  · intro l r initial hist hh he
    exact ⟨hist,hh,by simpa only [bitRun_zero] using he⟩
  · intro n ih l r initial hist hh he
    have hs:=named_left_any q q b w (bitRun n (bitValue b) l) r row
    have hsrc:namedLeft q (bitRun (n+1) (bitValue b) l) r=
     namedState q (bitRun n (bitValue b) l) (bitValue b+2*r) := by
      rw [bitRun_succ,namedLeft_cons]
    rw [←hsrc] at hs
    obtain ⟨middle,hm,hem⟩:=hs initial hist hh he
    obtain ⟨out,ho,hend⟩:=ih l (bitValue w+2*r) initial middle hm hem
    exact ⟨out,ho,by simpa only [bitRun_commute] using hend⟩
 exact hall n l r
end ZF209.BinaryTape
