module
public import ModelNativePairCore
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeTimesFour
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano ZF209.NativePair M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def expected (base:Nat) : Nat→Instruction
 | 0 => .dec 5 (base+6) (base+1)
 | 1 => .inc 2 (base+2)
 | 2 => .inc 2 (base+3)
 | 3 => .inc 2 (base+4)
 | 4 => .inc 2 (base+5)
 | _ => .jump base
structure Bound (base:Nat) : Prop where
 range : base+6<4341
 rows : ∀j:Fin 6,program (base+j.val)=some (expected base j.val)
variable {base:Nat} (hb:Bound base)
include hb
lemma step0_zero (ρ:Nat→M) (t w x y:M) :
 programStep (pairState base ρ 0 t w x 0) (pairState base ρ 6 t w x 0) := by
 refine ⟨base+0,by have hh:=hb.range;omega,rfl,.dec 5 (base+6) (base+1),?_,?_⟩
 · simpa [expected] using hb.rows ⟨0,by decide⟩
 · simp [NativeSource.execute,pairState,registerIndex]
lemma step0_dec (ρ:Nat→M) (t w x y:M) :
 programStep (pairState base ρ 0 t w x (y+1)) (pairState base ρ 1 t w x y) := by
 refine ⟨base+0,by have hh:=hb.range;omega,rfl,.dec 5 (base+6) (base+1),?_,?_⟩
 · simpa [expected] using hb.rows ⟨0,by decide⟩
 · unfold NativeSource.execute
   dsimp only
   rw [if_neg (show (pairState base ρ 0 t w x (y+1)).registers (registerIndex 5)≠0 from by change y+1≠0;simp)]
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma step1_inc (ρ:Nat→M) (t w x y:M) :
 programStep (pairState base ρ 1 t w x y) (pairState base ρ 2 (t+1) w x y) := by
 refine ⟨base+1,by have hh:=hb.range;omega,rfl,.inc 2 (base+2),?_,?_⟩
 · simpa [expected] using hb.rows ⟨1,by decide⟩
 · simp only [NativeSource.execute,pairState]
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma step2_inc (ρ:Nat→M) (t w x y:M) :
 programStep (pairState base ρ 2 t w x y) (pairState base ρ 3 (t+1) w x y) := by
 refine ⟨base+2,by have hh:=hb.range;omega,rfl,.inc 2 (base+3),?_,?_⟩
 · simpa [expected] using hb.rows ⟨2,by decide⟩
 · simp only [NativeSource.execute,pairState]
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma step3_inc (ρ:Nat→M) (t w x y:M) :
 programStep (pairState base ρ 3 t w x y) (pairState base ρ 4 (t+1) w x y) := by
 refine ⟨base+3,by have hh:=hb.range;omega,rfl,.inc 2 (base+4),?_,?_⟩
 · simpa [expected] using hb.rows ⟨3,by decide⟩
 · simp only [NativeSource.execute,pairState]
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma step4_inc (ρ:Nat→M) (t w x y:M) :
 programStep (pairState base ρ 4 t w x y) (pairState base ρ 5 (t+1) w x y) := by
 refine ⟨base+4,by have hh:=hb.range;omega,rfl,.inc 2 (base+5),?_,?_⟩
 · simpa [expected] using hb.rows ⟨4,by decide⟩
 · simp only [NativeSource.execute,pairState]
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma step5_jump (ρ:Nat→M) (t w x y:M) :
 programStep (pairState base ρ 5 t w x y) (pairState base ρ 0 t w x y) := by
 refine ⟨base+5,by have hh:=hb.range;omega,rfl,.jump base,?_,?_⟩
 · simpa [expected] using hb.rows ⟨5,by decide⟩
 · simp [NativeSource.execute,pairState,registerIndex]
omit hb in
def terminates (base:Nat) (ρ:Nat→M) (y:M) : Prop := ∀t w x:M,
 nativeReaches (pairState base ρ 0 t w x y) (pairState base ρ 6 (t+4*y) w x 0)
omit hb in
noncomputable def timesFormula (base:Nat) : ArithmeticSemiformula Nat 1 :=
 “y. ∀t, ∀w, ∀x, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head ↑base w &1 t &3 &4 y &6 &7 x) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !stateGraph last ↑(base+6) w &1 (t+4*y) &3 &4 0 &6 &7 x”
omit hb in
lemma timesFormula_eval (base:Nat) (ρ:Nat→M) (y:M) : (timesFormula base).Eval ![y] ρ ↔ terminates base ρ y := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [timesFormula,terminates,nativeReaches,pairState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval,numeral_eq_natCast]
omit hb in
noncomputable def times_certificate (base:Nat) (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>terminates base ρ (v 0)) := by
 refine ⟨timesFormula base,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (timesFormula_eval base ρ (v 0)).symm
theorem native_times4 (ρ:Nat→M) : ∀y:M,terminates base ρ y := by
 apply (times_certificate base ρ).induction
 · change terminates base ρ 0
   intro t w x
   change nativeReaches _ (pairState base ρ 6 (t+4*0) w x 0)
   rw [mul_zero,add_zero]
   exact nativeReaches_step (step0_zero hb ρ t w x 0)
 · intro y ih
   change terminates base ρ y at ih
   change terminates base ρ (y+1)
   intro t w x
   have h1:=nativeReaches_step (step0_dec hb ρ t w x y)
   have h2:=nativeReaches_step (step1_inc hb ρ t w x y)
   have h3:=nativeReaches_step (step2_inc hb ρ (t+1) w x y)
   have h4:=nativeReaches_step (step3_inc hb ρ ((t+1)+1) w x y)
   have h5:=nativeReaches_step (step4_inc hb ρ (((t+1)+1)+1) w x y)
   have h6:=nativeReaches_step (step5_jump hb ρ ((((t+1)+1)+1)+1) w x y)
   have ht:=ih ((((t+1)+1)+1)+1) w x
   change nativeReaches _ (pairState base ρ 6 (((((t+1)+1)+1)+1)+4*y) w x 0) at ht
   have he:(((((t+1)+1)+1)+1)+4*y)=t+4*(y+1) := by
    simp only [mul_add,mul_one]
    have h4:(4:M)=((1+1)+1)+1:=by norm_num
    simp only [h4]
    ac_rfl
   rw [he] at ht
   exact nativeReaches_trans h1 (nativeReaches_trans h2 (nativeReaches_trans h3 (nativeReaches_trans h4 (nativeReaches_trans h5 (nativeReaches_trans h6 ht)))))
omit hb in
lemma bound_4283 : Bound 4283 := by constructor <;> decide
end ZF209.NativeTimesFour
