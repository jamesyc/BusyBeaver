module
public import ModelNativeUnpair
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeTransfer
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
structure Bound (base:Nat) (src dst:Fin 9) : Prop where
 range : base+3<4341
 distinct : src≠dst
 row0 : program base=some (.dec src.val (base+3) (base+1))
 row1 : program (base+1)=some (.inc dst.val (base+2))
 row2 : program (base+2)=some (.jump base)
noncomputable def transferState (src dst:Fin 9) (ρ:Nat→M) (pc y x:M) : NativeSource.State M :=
 ⟨pc,fun j=>if j=src then y else if j=dst then x else ρ j.val⟩
def fieldTerm (src dst:Fin 9) (j:Fin 9) : ArithmeticSemiterm Nat 4 :=
 if j=src then Semiterm.bvar 2 else if j=dst then Semiterm.bvar 3 else Semiterm.fvar j.val
def transferCfgGraph (src dst:Fin 9) : ArithmeticSemiformula Nat 4 :=
 Rew.bind (fun i:Fin 11 => Fin.cases (Semiterm.bvar 0)
   (fun i=>Fin.cases (Semiterm.bvar 1) (fieldTerm src dst) i) i) Empty.elim ▹ stateGraph
lemma transferCfgGraph_eval (src dst:Fin 9) (ρ:Nat→M) (code pc y x:M) :
 (transferCfgGraph src dst).Eval ![code,pc,y,x] ρ ↔ code=stateCode (transferState src dst ρ pc y x) := by
 have hfield (j:Fin 9) : Semiterm.val ![code,pc,y,x] ρ (fieldTerm src dst j)=
   if j=src then y else if j=dst then x else ρ j.val := by
  by_cases hs:j=src <;> by_cases hd:j=dst <;> simp_all [fieldTerm] <;> rfl
 have hvec : (fun j:Fin 9=>if j=src then y else if j=dst then x else ρ j.val)=
 ![(if (0:Fin 9)=src then y else if (0:Fin 9)=dst then x else ρ 0),
 (if (1:Fin 9)=src then y else if (1:Fin 9)=dst then x else ρ 1),
 (if (2:Fin 9)=src then y else if (2:Fin 9)=dst then x else ρ 2),
 (if (3:Fin 9)=src then y else if (3:Fin 9)=dst then x else ρ 3),
 (if (4:Fin 9)=src then y else if (4:Fin 9)=dst then x else ρ 4),
 (if (5:Fin 9)=src then y else if (5:Fin 9)=dst then x else ρ 5),
 (if (6:Fin 9)=src then y else if (6:Fin 9)=dst then x else ρ 6),
 (if (7:Fin 9)=src then y else if (7:Fin 9)=dst then x else ρ 7),
 (if (8:Fin 9)=src then y else if (8:Fin 9)=dst then x else ρ 8)] := by
  funext j
  rcases j with ⟨j,hj⟩
  have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
  rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> rfl
 simp only [transferCfgGraph,Semiformula.eval_rew]
 have hv : Semiterm.val ![code,pc,y,x] ρ ∘
   (fun i : Fin 11 => Fin.cases (Semiterm.bvar 0) (fun i=>Fin.cases (Semiterm.bvar 1) (fieldTerm src dst) i) i) =
   code :> pc :> (fun j:Fin 9=>if j=src then y else if j=dst then x else ρ j.val) := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  exact hfield j
 simp only [Rew.bind_bvar,Rew.bind_fvar,Function.comp_def] at *
 rw [hv,hvec]
 simpa only [transferState,hvec,Empty.eq_elim] using stateGraph_eval code pc _ _ _ _ _ _ _ _ _
variable {base:Nat} {src dst:Fin 9}
lemma step_zero (hb:Bound base src dst) (ρ:Nat→M) (x:M) :
 programStep (transferState src dst ρ (base:M) 0 x) (transferState src dst ρ ((base+3:Nat):M) 0 x) := by
 refine ⟨base,by have hh:=hb.range;omega,rfl,.dec src.val (base+3) (base+1),hb.row0,?_⟩
 have hi:registerIndex src.val=src:=by apply Fin.ext; exact Nat.mod_eq_of_lt src.isLt
 simp [NativeSource.execute,transferState,hi]
lemma step_dec (hb:Bound base src dst) (ρ:Nat→M) (y x:M) :
 programStep (transferState src dst ρ (base:M) (y+1) x) (transferState src dst ρ ((base+1:Nat):M) y x) := by
 refine ⟨base,by have hh:=hb.range;omega,rfl,.dec src.val (base+3) (base+1),hb.row0,?_⟩
 have hi:registerIndex src.val=src:=by apply Fin.ext; exact Nat.mod_eq_of_lt src.isLt
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (transferState src dst ρ (base:M) (y+1) x).registers (registerIndex src.val)≠0 from by simp [transferState,hi])]
 congr 2
 funext j
 have hj:j.val=src.val ↔ j=src := Fin.ext_iff.symm
 by_cases hs:j=src <;> by_cases hd:j=dst <;> simp_all [transferState,modelPredecessor_succ]
lemma step_inc (hb:Bound base src dst) (ρ:Nat→M) (y x:M) :
 programStep (transferState src dst ρ ((base+1:Nat):M) y x) (transferState src dst ρ ((base+2:Nat):M) y (x+1)) := by
 refine ⟨base+1,by have hh:=hb.range;omega,rfl,.inc dst.val (base+2),hb.row1,?_⟩
 simp only [NativeSource.execute]
 congr 2
 funext j
 have hj:j.val=dst.val ↔ j=dst := Fin.ext_iff.symm
 have hs:src≠dst:=hb.distinct
 by_cases hjs:j=src <;> by_cases hjd:j=dst <;> simp_all [transferState,hj]
lemma step_jump (hb:Bound base src dst) (ρ:Nat→M) (y x:M) :
 programStep (transferState src dst ρ ((base+2:Nat):M) y x) (transferState src dst ρ (base:M) y x) := by
 refine ⟨base+2,by have hh:=hb.range;omega,rfl,.jump base,hb.row2,?_⟩
 rfl
def terminates (base:Nat) (src dst:Fin 9) (ρ:Nat→M) (y:M) : Prop := ∀x:M,
 nativeReaches (transferState src dst ρ (base:M) y x) (transferState src dst ρ ((base+3:Nat):M) 0 (x+y))
noncomputable def transferFormula (base:Nat) (src dst:Fin 9) : ArithmeticSemiformula Nat 1 :=
 “y. ∀x, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧ !(transferCfgGraph src dst) head ↑base y x) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !(transferCfgGraph src dst) last ↑(base+3) 0 (x+y)”
lemma transferFormula_eval (base:Nat) (src dst:Fin 9) (ρ:Nat→M) (y:M) :
 (transferFormula base src dst).Eval ![y] ρ ↔ terminates base src dst ρ y := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [transferFormula,terminates,nativeReaches,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,transferCfgGraph_eval,numeral_eq_natCast]
noncomputable def transfer_certificate (base:Nat) (src dst:Fin 9) (ρ:Nat→M) :
 FormulaCertificate ρ 1 (fun v=>terminates base src dst ρ (v 0)) := by
 refine ⟨transferFormula base src dst,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (transferFormula_eval base src dst ρ (v 0)).symm
/-- Reusable exact three-row source loop, certified at arbitrary register positions. -/
theorem native_transfer (hb:Bound base src dst) (ρ:Nat→M) : ∀y:M,terminates base src dst ρ y := by
 apply (transfer_certificate base src dst ρ).induction
 · change terminates base src dst ρ 0
   intro x
   change nativeReaches _ (transferState src dst ρ ((base+3:Nat):M) 0 (x+0))
   rw [add_zero]
   exact nativeReaches_step (step_zero hb ρ x)
 · intro y ih
   change terminates base src dst ρ y at ih
   change terminates base src dst ρ (y+1)
   intro x
   have ht:=ih (x+1)
   change nativeReaches _ (transferState src dst ρ ((base+3:Nat):M) 0 ((x+1)+y)) at ht
   have he:(x+1)+y=x+(y+1):=by ac_rfl
   rw [he] at ht
   exact nativeReaches_trans (nativeReaches_step (step_dec hb ρ y x))
    (nativeReaches_trans (nativeReaches_step (step_inc hb ρ y x))
    (nativeReaches_trans (nativeReaches_step (step_jump hb ρ y (x+1))) ht))
end ZF209.NativeTransfer
