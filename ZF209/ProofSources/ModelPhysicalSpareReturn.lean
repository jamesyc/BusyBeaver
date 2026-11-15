module
public import ModelPhysicalSpareCarry
public import ModelPhysicalReturnBlocks
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def spareReverseBlueprint : PR.Blueprint 1 where
 zero := .mkSigma “z l. z=l”
 succ := .mkSigma “u z i l. u=3+8*z”
noncomputable def spareReverseConstruction : PR.Construction M spareReverseBlueprint where
 zero := fun v=>v 0
 succ := fun _ _ z=>3+8*z
 zero_defined := .mk (by intro v; simp [spareReverseBlueprint])
 succ_defined := .mk (by intro v; simp [spareReverseBlueprint,numeral_eq_natCast])
noncomputable def spareReverse (n l:M) : M := spareReverseConstruction.result ![l] n
def spareReverseGraph : 𝚺ᴬ₁.Semisentence 3 := spareReverseBlueprint.resultDef
lemma spareReverse_defined : 𝚺ᴬ₁.DefinedFunction₂ (spareReverse (M:=M)) spareReverseGraph := .mk (by
 intro v
 have hv:v=![v 0,v 1,v 2] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]; exact spareReverseConstruction.result_defined_iff _)
instance spareReverse_definable : 𝚺ᴬ₁-Function₂ (spareReverse (M:=M)) := spareReverse_defined.to_definable
lemma spareReverse_zero (l:M) : spareReverse 0 l=l := spareReverseConstruction.result_zero ![l]
lemma spareReverse_succ (n l:M) : spareReverse (n+1) l=3+8*spareReverse n l := spareReverseConstruction.result_succ ![l] n
lemma registerBlockLeft_one (l:M) : registerBlockLeft 1 l=3+8*l := by
 unfold registerBlockLeft
 have h1:(1:M)=0+1 := by simp
 rw [bitRun_succ,h1,bitRun_succ,bitRun_zero]
 simp only [mul_add,mul_one,←mul_assoc]
 norm_num
 rw [←add_assoc]
 norm_num
lemma spareCarry_restore (n l:M) : 1+2*spareCarry n l=spareReverse n (1+2*l) := by
 induction n using ISigma1.sigma1_succ_induction
 · definability
 case zero => rw [spareCarry_zero,spareReverse_zero]
 case succ n ih =>
  rw [spareCarry_succ,spareReverse_succ,←ih]
  simp only [mul_add,←mul_assoc]
  norm_num
  rw [←add_assoc,←add_assoc]
  norm_num

def leftStateGraph (q:Nat) : ArithmeticSemisentence 3 :=
 let k:=M209.forward q
 “z l r. ∃b, ∃t, !lowBitGraph b l ∧ !tailBitsGraph t l ∧ !stateGraph z ↑k t (b+2*r)”
lemma leftStateGraph_eval (q:Nat) (z l r:M) :
 (leftStateGraph q).Evalb ![z,l,r] ↔ z=stateCode (namedLeft q l r) := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 have hl (b l:M) : lowBitGraph.val.Evalb ![b,l] ↔ b=lowBit l := graphValue_spec lowBitGraph lowBitGraph_total b ![l]
 have ht (t l:M) : tailBitsGraph.val.Evalb ![t,l] ↔ t=tailBits l := graphValue_spec tailBitsGraph tailBitsGraph_total t ![l]
 simp [leftStateGraph,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,
 Empty.eq_elim,hv,hl,ht,stateGraph_eval,namedLeft,namedState,numeral_eq_natCast]
def ReturnSpares (n:M) : Prop := ∀l r initial hist:M,
 runHistory initial hist → modelListHead hist=stateCode (namedLeft 40 (spareReverse n l) r) →
 ∃out,runHistory initial out ∧ modelListHead out=stateCode (namedLeft 40 l (spareRun n r))
def returnSparesFormulaOf (run:ArithmeticSemisentence 2) (spares rev:𝚺ᴬ₁.Semisentence 3) : ArithmeticSemiformula Nat 1 :=
 let left:=leftStateGraph 40
 “n. ∀l, ∀r, ∀initial, ∀hist, ∀right, ∀ls, ∀before, ∀after,
 !spares right n r → !rev ls n l → !left before ls r → !left after l right →
 !run initial hist → !listHeadGraph before hist → ∃out,!run initial out ∧ !listHeadGraph after out”
lemma returnSparesFormula_eval (ρ:Nat→M) (n:M) :
 (returnSparesFormulaOf physicalRunFormula spareRunGraph spareReverseGraph).Eval ![n] ρ ↔ ReturnSpares n := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [returnSparesFormulaOf,ReturnSpares,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Empty.eq_elim,hv,spareRun_defined.iff,spareReverse_defined.iff,leftStateGraph_eval,physicalRunFormula_eval,
 ruleHead_defined.iff,numeral_eq_natCast]
 constructor
 · intro h l r initial hist hh he
   obtain ⟨out,ho,hend⟩:=h l r initial hist _ _ _ _ rfl rfl rfl rfl hh he.symm
   exact ⟨out,ho,hend.symm⟩
 · intro h l r initial hist right ls before after hr hl hb ha hh he
   rw [hr] at ha; rw [hl] at hb
   obtain ⟨out,ho,hend⟩:=h l r initial hist hh (he.symm.trans hb)
   exact ⟨out,ho,ha.trans hend.symm⟩
lemma native_return_spares : ∀n:M,ReturnSpares n := by
 haveI : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔)
 refine InductionScheme.succ_induction (C:=Set.univ) (P:=ReturnSpares) ?_ ?_ ?_
 · exact ⟨(fun _=>0),returnSparesFormulaOf physicalRunFormula spareRunGraph spareReverseGraph,by trivial,
    fun n=>(returnSparesFormula_eval (fun _=>0) n).symm⟩
 · intro l r initial hist hh he
   exact ⟨hist,hh,by simpa only [spareRun_zero,spareReverse_zero] using he⟩
 · intro n ih l r initial hist hh he
   have hs:=named_return_block 54 40 40 (1:M) (spareReverse n l) r (by decide +kernel) (by decide +kernel) (by decide +kernel)
   rw [registerBlockLeft_one,←spareReverse_succ,registerBlock_one] at hs
   obtain ⟨middle,hm,hem⟩:=hs initial hist hh he
   obtain ⟨out,ho,hend⟩:=ih l (6+8*r) initial middle hm hem
   exact ⟨out,ho,by simpa only [spareRun_commute] using hend⟩
lemma native_spare_return (n l r:M) :
 Reaches (namedLeft 40 (spareReverse n l) r) (namedLeft 40 l (spareRun n r)) := native_return_spares n l r
attribute [irreducible] spareReverseGraph
end ZF209.BinaryTape
