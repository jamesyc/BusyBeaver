module
public import ModelPhysicalCarryBlock
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def spareCarryBlueprint : PR.Blueprint 1 where
 zero := .mkSigma “z l. z=l”
 succ := .mkSigma “u z i l. u=5+8*z”
noncomputable def spareCarryConstruction : PR.Construction M spareCarryBlueprint where
 zero := fun v=>v 0
 succ := fun _ _ z=>5+8*z
 zero_defined := .mk (by intro v; simp [spareCarryBlueprint])
 succ_defined := .mk (by intro v; simp [spareCarryBlueprint,numeral_eq_natCast])
noncomputable def spareCarry (n l:M) : M := spareCarryConstruction.result ![l] n
def spareCarryGraph : 𝚺ᴬ₁.Semisentence 3 := spareCarryBlueprint.resultDef
lemma spareCarry_defined : 𝚺ᴬ₁.DefinedFunction₂ (spareCarry (M:=M)) spareCarryGraph := .mk (by
 intro v
 have hv:v=![v 0,v 1,v 2] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]; exact spareCarryConstruction.result_defined_iff _)
instance spareCarry_definable : 𝚺ᴬ₁-Function₂ (spareCarry (M:=M)) := spareCarry_defined.to_definable
lemma spareCarry_zero (l:M) : spareCarry 0 l=l := spareCarryConstruction.result_zero ![l]
lemma spareCarry_succ (n l:M) : spareCarry (n+1) l=5+8*spareCarry n l := spareCarryConstruction.result_succ ![l] n
lemma spareCarry_commute (n l:M) : spareCarry n (5+8*l)=spareCarry (n+1) l := by
 induction n using ISigma1.sigma1_succ_induction
 · definability
 case zero => rw [spareCarry_zero,spareCarry_succ,spareCarry_zero]
 case succ n ih => rw [spareCarry_succ,ih,spareCarry_succ (n+1)]
lemma carryBlockLeft_one (l:M) : carryBlockLeft 1 l=5+8*l := by
 have h1:(1:M)=0+1 := by simp
 unfold carryBlockLeft
 rw [h1,bitRun_succ,bitRun_zero]
 simp only [zero_add,mul_add,←mul_assoc]
 norm_num
 rw [←add_assoc]
 norm_num

def CarrySpares (n:M) : Prop := ∀l r initial hist:M,
 runHistory initial hist → modelListHead hist=stateCode (namedState 0 l (spareRun n r)) →
 ∃out,runHistory initial out ∧ modelListHead out=stateCode (namedState 0 (spareCarry n l) r)
def carrySparesFormulaOf (run:ArithmeticSemisentence 2) (spares carry:𝚺ᴬ₁.Semisentence 3) : ArithmeticSemiformula Nat 1 :=
 let q:=M209.forward 0
 “n. ∀l, ∀r, ∀initial, ∀hist, ∀right, ∀left, ∀before, ∀after,
 !spares right n r → !carry left n l →
 !stateGraph before ↑q l right → !stateGraph after ↑q left r →
 !run initial hist → !listHeadGraph before hist → ∃out,!run initial out ∧ !listHeadGraph after out”
lemma carrySparesFormula_eval (ρ:Nat→M) (n:M) :
 (carrySparesFormulaOf physicalRunFormula spareRunGraph spareCarryGraph).Eval ![n] ρ ↔ CarrySpares n := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [carrySparesFormulaOf,CarrySpares,namedState,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Empty.eq_elim,hv,spareRun_defined.iff,spareCarry_defined.iff,stateGraph_eval,physicalRunFormula_eval,
 ruleHead_defined.iff,numeral_eq_natCast]
 constructor
 · intro h l r initial hist hh he
   obtain ⟨out,ho,hend⟩:=h l r initial hist _ _ _ _ rfl rfl rfl rfl hh he.symm
   exact ⟨out,ho,hend.symm⟩
 · intro h l r initial hist right left before after hr hl hb ha hh he
   rw [hr] at hb; rw [hl] at ha
   obtain ⟨out,ho,hend⟩:=h l r initial hist hh (he.symm.trans hb)
   exact ⟨out,ho,ha.trans hend.symm⟩
/-- Physical carry across the complete internally sized spare suffix, not a fixed
external list of spares. Actual native0/94 loop and literal209 scans are used. -/
lemma native_carry_spares : ∀n:M,CarrySpares n := by
 haveI : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔)
 refine InductionScheme.succ_induction (C:=Set.univ) (P:=CarrySpares) ?_ ?_ ?_
 · exact ⟨(fun _=>0),carrySparesFormulaOf physicalRunFormula spareRunGraph spareCarryGraph,by trivial,
    fun n=>(carrySparesFormula_eval (fun _=>0) n).symm⟩
 · intro l r initial hist hh he
   exact ⟨hist,hh,by simpa only [spareRun_zero,spareCarry_zero] using he⟩
 · intro n ih l r initial hist hh he
   have hs:=native_carry_block (1:M) l (spareRun n r)
   rw [registerBlock_one,←spareRun_succ,carryBlockLeft_one] at hs
   obtain ⟨middle,hm,hem⟩:=hs initial hist hh he
   obtain ⟨out,ho,hend⟩:=ih (5+8*l) r initial middle hm hem
   exact ⟨out,ho,by simpa only [spareCarry_commute] using hend⟩
attribute [irreducible] spareCarryGraph
end ZF209.BinaryTape
