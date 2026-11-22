module
public import ZF192Support.Execution.Registers.Arithmetic.Footprints
public import ZF192Support.Execution.Registers.Arithmetic.Transfer

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.NativeCopyLoop
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano RegisterMachine.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def registers {α : Type*} (src dst scratch : Fin 9) (ρ : Nat → α) (n d t : α) (j : Fin 9) : α :=
  if j = src then n else if j = dst then d else if j = scratch then t else ρ j.val

def state (src dst scratch : Fin 9) (ρ : Nat → M) (pc n d t : M) : NativeSource.State M :=
  ⟨pc, registers src dst scratch ρ n d t⟩

variable {base : Nat} {src dst scratch : Fin 9}

private lemma step_zero (hb : Bound base src dst scratch) (ρ : Nat → M) (d t : M) :
    programStep (state src dst scratch ρ (base:M) 0 d t)
      (state src dst scratch ρ ((base+4:Nat):M) 0 d t) := by
  refine ⟨base, by have := hb.range; omega, rfl, _, hb.dec, ?_⟩
  have hi : registerIndex src.val = src := Fin.ext (Nat.mod_eq_of_lt src.isLt)
  simp [NativeSource.execute, state, registers, hi]

private lemma step_dec (hb : Bound base src dst scratch) (ρ : Nat → M) (n d t : M) :
    programStep (state src dst scratch ρ (base:M) (n+1) d t)
      (state src dst scratch ρ ((base+1:Nat):M) n d t) := by
  refine ⟨base, by have := hb.range; omega, rfl, _, hb.dec, ?_⟩
  have hi : registerIndex src.val = src := Fin.ext (Nat.mod_eq_of_lt src.isLt)
  simp only [NativeSource.execute, state, registers, hi, ite_true, add_ne_zero.mpr (Or.inr one_ne_zero),
    ite_false, Option.some.injEq, NativeSource.State.mk.injEq, true_and]
  funext j
  have hval : j.val = src.val ↔ j = src := Fin.ext_iff.symm
  by_cases h : j = src <;> simp [registers, hval, h, modelPredecessor_succ]

private lemma step_incDst (hb : Bound base src dst scratch) (ρ : Nat → M) (n d t : M) :
    programStep (state src dst scratch ρ ((base+1:Nat):M) n d t)
      (state src dst scratch ρ ((base+2:Nat):M) n (d+1) t) := by
  refine ⟨base+1, by have := hb.range; omega, rfl, _, hb.incDst, ?_⟩
  simp only [NativeSource.execute, state, Option.some.injEq, NativeSource.State.mk.injEq, true_and]
  funext j
  have hval : j.val = dst.val ↔ j = dst := Fin.ext_iff.symm
  by_cases h : j = dst <;> simp [registers, hval, h, Ne.symm hb.srcDst]

private lemma step_incScratch (hb : Bound base src dst scratch) (ρ : Nat → M) (n d t : M) :
    programStep (state src dst scratch ρ ((base+2:Nat):M) n d t)
      (state src dst scratch ρ ((base+3:Nat):M) n d (t+1)) := by
  refine ⟨base+2, by have := hb.range; omega, rfl, _, hb.incScratch, ?_⟩
  simp only [NativeSource.execute, state, Option.some.injEq, NativeSource.State.mk.injEq, true_and]
  funext j
  have hval : j.val = scratch.val ↔ j = scratch := Fin.ext_iff.symm
  by_cases h : j = scratch <;> simp [registers, hval, h, Ne.symm hb.srcScratch, Ne.symm hb.dstScratch]

private lemma step_jump (hb : Bound base src dst scratch) (ρ : Nat → M) (n d t : M) :
    programStep (state src dst scratch ρ ((base+3:Nat):M) n d t)
      (state src dst scratch ρ (base:M) n d t) :=
  ⟨base+3, hb.range, rfl, _, hb.jump, rfl⟩

private def cfgGraph (src dst scratch : Fin 9) : ArithmeticSemiformula Nat 5 :=
  Rew.bind (fun i : Fin 11 => Fin.cases (Semiterm.bvar 0)
    (fun j => Fin.cases (Semiterm.bvar 1)
      (registers src dst scratch Semiterm.fvar (Semiterm.bvar 2) (Semiterm.bvar 3) (Semiterm.bvar 4)) j) i)
    Empty.elim ▹ stateGraph

private lemma cfgGraph_eval (ρ : Nat → M) (code pc n d t : M) :
    (cfgGraph src dst scratch).Eval ![code,pc,n,d,t] ρ ↔
      code = stateCode (state src dst scratch ρ pc n d t) := by
  have fields (i : Fin 9) :
      Semiterm.val (L := ℒₒᵣ) ![code,pc,n,d,t] ρ
        (registers src dst scratch Semiterm.fvar (Semiterm.bvar 2) (Semiterm.bvar 3) (Semiterm.bvar 4) i) =
      registers src dst scratch ρ n d t i := by
    unfold registers
    by_cases hs : i = src
    · simp only [ite_eq_left hs]
      rfl
    · simp only [ite_eq_right hs]
      by_cases hd : i = dst
      · simp only [ite_eq_left hd]
        rfl
      · simp only [ite_eq_right hd]
        by_cases ht : i = scratch
        · simp only [ite_eq_left ht]
          rfl
        · simp only [ite_eq_right ht]
          rfl
  have evalFields :
      Semiterm.val (L := ℒₒᵣ) ![code,pc,n,d,t] ρ ∘
        (fun i : Fin 11 => Fin.cases (Semiterm.bvar 0)
          (fun j => Fin.cases (Semiterm.bvar 1)
            (registers src dst scratch Semiterm.fvar (Semiterm.bvar 2) (Semiterm.bvar 3)
              (Semiterm.bvar 4)) j) i) =
      code :> pc :> registers src dst scratch ρ n d t := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl fields j
  let r := registers src dst scratch ρ n d t
  have vector : r = ![r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8] := by
    funext i
    rcases i with ⟨i, hi⟩
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
    rcases h with h|h|h|h|h|h|h|h|h <;> subst i <;> rfl
  simp only [cfgGraph, Semiformula.eval_rew, Rew.bind_bvar, Rew.bind_fvar, Function.comp_def] at *
  rw [evalFields]
  change stateGraph.Eval (code :> pc :> r) _ ↔ code = stateCode ⟨pc,r⟩
  rw [vector]
  exact stateGraph_eval code pc _ _ _ _ _ _ _ _ _

def drainTerminates (base : Nat) (src dst scratch : Fin 9) (ρ : Nat → M) (n : M) : Prop :=
  ∀ d t : M, nativeReaches (state src dst scratch ρ (base:M) n d t)
    (state src dst scratch ρ ((base+4:Nat):M) 0 (d+n) (t+n))

private noncomputable def drainFormula (base : Nat) (src dst scratch : Fin 9) : ArithmeticSemiformula Nat 1 :=
  “n. ∀d, ∀t, ∀initial, ∀hist, ∀head,
    (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
      !(cfgGraph src dst scratch) head ↑base n d t) →
    ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
      !(cfgGraph src dst scratch) last ↑(base+4) 0 (d+n) (t+n)”

private noncomputable def drainCertificate (base : Nat) (src dst scratch : Fin 9) (ρ : Nat → M) :
    FormulaCertificate ρ 1 (fun v => drainTerminates base src dst scratch ρ (v 0)) := by
  refine ⟨drainFormula base src dst scratch, ?_⟩
  intro v
  simp [drainFormula, drainTerminates, nativeReaches, Semiformula.eval_rew, Function.comp_def,
    Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton, Empty.eq_elim, nativeRunFormula_eval,
    ruleHead_defined.iff, cfgGraph_eval, numeral_eq_natCast]

theorem drain_terminates (hb : Bound base src dst scratch) (ρ : Nat → M) :
    ∀ n : M, drainTerminates base src dst scratch ρ n := by
  apply (drainCertificate base src dst scratch ρ).induction
  · change drainTerminates base src dst scratch ρ 0
    intro d t
    change nativeReaches _ (state src dst scratch ρ ((base+4:Nat):M) 0 (d+0) (t+0))
    rw [add_zero, add_zero]
    exact nativeReaches_step (step_zero hb ρ d t)
  · intro n ih
    change drainTerminates base src dst scratch ρ n at ih
    change drainTerminates base src dst scratch ρ (n+1)
    intro d t
    have hd := nativeReaches_trans (nativeReaches_step (step_dec hb ρ n d t))
      (nativeReaches_trans (nativeReaches_step (step_incDst hb ρ n d t))
      (nativeReaches_trans (nativeReaches_step (step_incScratch hb ρ n (d+1) t))
        (nativeReaches_step (step_jump hb ρ n (d+1) (t+1)))))
    have ht := ih (d+1) (t+1)
    change nativeReaches _ (state src dst scratch ρ ((base+4:Nat):M) 0 ((d+1)+n) ((t+1)+n)) at ht
    have add (z : M) : z+1+n = z+(n+1) := by ac_rfl
    rw [add d, add t] at ht
    exact nativeReaches_trans hd ht

theorem native_copy (hb : CopyBound base src dst scratch) (ρ : Nat → M) (n d : M) :
    nativeReaches (state src dst scratch ρ (base:M) n d 0)
      (state src dst scratch ρ ((base+7:Nat):M) n (d+n) 0) := by
  have hd := drain_terminates hb.drain ρ n d 0
  change nativeReaches _ (state src dst scratch ρ ((base+4:Nat):M) 0 (d+n) (0+n)) at hd
  rw [zero_add] at hd
  let frame : Nat → M := fun i => if i = dst.val then d+n else ρ i
  have hr := NativeTransfer.native_transfer hb.restore frame n 0
  change nativeReaches (NativeTransfer.transferState scratch src frame ((base+4:Nat):M) n 0)
    (NativeTransfer.transferState scratch src frame ((base+7:Nat):M) 0 (0+n)) at hr
  rw [zero_add] at hr
  apply nativeReaches_trans hd
  convert hr using 1 <;>
    simp only [state, NativeTransfer.transferState, NativeSource.State.mk.injEq, true_and] <;>
    funext i
  all_goals
    have hsd := hb.drain.srcDst
    have hst := hb.drain.srcScratch
    have hdt := hb.drain.dstScratch
    have hval : i.val = dst.val ↔ i = dst := Fin.ext_iff.symm
    by_cases hs : i = src <;> by_cases hd : i = dst <;> by_cases hx : i = scratch <;>
      simp_all [registers, frame, hval]

end ZF192Support.NativeCopyLoop
