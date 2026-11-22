module
public import ZF192Support.Execution.Registers.Arithmetic.Transfer

@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.NativeUnpair
open NativeSource ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano RegisterMachine.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The Cantor loop counts down in `input` and keeps its coordinates in registers 8 and 5. -/
structure Bound (base : Nat) (input : Fin 9) : Prop where
  range : base + 8 < 4341
  input_ne_x : input.val ≠ 8
  input_ne_y : input.val ≠ 5
  countdown : program base = some (.dec input.val (base + 8) (base + 1))
  advanceY : program (base + 1) = some (.inc 5 (base + 2))
  testX : program (base + 2) = some (.dec 8 (base + 4) (base + 3))
  skipTransfer : program (base + 3) = some (.jump (base + 7))
  transfer : NativeTransfer.Bound (base + 4) 5 8
  loop : program (base + 7) = some (.jump base)

def registers (input : Fin 9) (ρ : Nat → M) (w x y : M) (j : Fin 9) : M :=
  if j.val = input.val then w else if j.val = 8 then x else if j.val = 5 then y else ρ j.val

def state (input : Fin 9) (ρ : Nat → M) (pc w x y : M) : State M :=
  ⟨pc, registers input ρ w x y⟩

variable {base : Nat} {input : Fin 9} (hb : Bound base input)

private theorem index_val (r : Fin 9) : registerIndex r.val = r :=
  Fin.ext (Nat.mod_eq_of_lt r.isLt)

include hb in
private theorem countdown_zero (ρ : Nat → M) (x y : M) :
    programStep (state input ρ (base : M) 0 x y)
      (state input ρ ((base + 8 : Nat) : M) 0 x y) := by
  refine ⟨base, by have := hb.range; omega, rfl, _, hb.countdown, ?_⟩
  simp [NativeSource.execute, state, registers, index_val]

include hb in
private theorem countdown_step (ρ : Nat → M) (w x y : M) :
    programStep (state input ρ (base : M) (w + 1) x y)
      (state input ρ ((base + 1 : Nat) : M) w x y) := by
  refine ⟨base, by have := hb.range; omega, rfl, _, hb.countdown, ?_⟩
  have hn : (state input ρ (base : M) (w+1) x y).registers (registerIndex input.val) ≠ 0 := by
    simp [state, registers, index_val]
  rw [NativeSource.execute, if_neg hn]
  simp only [state]
  congr 2
  funext j
  by_cases h : j.val = input.val <;> simp [registers, h, modelPredecessor_succ]

include hb in
private theorem advance_y (ρ : Nat → M) (w x y : M) :
    programStep (state input ρ ((base + 1 : Nat) : M) w x y)
      (state input ρ ((base + 2 : Nat) : M) w x (y + 1)) := by
  refine ⟨base + 1, by have := hb.range; omega, rfl, _, hb.advanceY, ?_⟩
  simp only [NativeSource.execute, state, registers]
  congr 2
  funext j
  by_cases h : j.val = 5
  · simp [registers, h, Ne.symm hb.input_ne_y]
  · simp [registers, h]

include hb in
private theorem test_zero (ρ : Nat → M) (w y : M) :
    programStep (state input ρ ((base + 2 : Nat) : M) w 0 y)
      (state input ρ ((base + 4 : Nat) : M) w 0 y) := by
  refine ⟨base + 2, by have := hb.range; omega, rfl, _, hb.testX, ?_⟩
  simp [NativeSource.execute, state, registers, registerIndex, Ne.symm hb.input_ne_x]

include hb in
private theorem test_positive (ρ : Nat → M) (w x y : M) :
    programStep (state input ρ ((base + 2 : Nat) : M) w (x + 1) y)
      (state input ρ ((base + 3 : Nat) : M) w x y) := by
  refine ⟨base + 2, by have := hb.range; omega, rfl, _, hb.testX, ?_⟩
  have hn : (state input ρ ((base + 2 : Nat) : M) w (x+1) y).registers (registerIndex 8) ≠ 0 := by
    simp [state, registers, registerIndex, Ne.symm hb.input_ne_x]
  simp only [NativeSource.execute, if_neg hn]
  congr 2
  funext j
  by_cases h : j.val = 8
  · simp [h, state, registers, Ne.symm hb.input_ne_x, modelPredecessor_succ]
  · simp [h, state, registers]

include hb in
private theorem skip (ρ : Nat → M) (w x y : M) :
    programStep (state input ρ ((base + 3 : Nat) : M) w x y)
      (state input ρ ((base + 7 : Nat) : M) w x y) :=
  ⟨base + 3, by have := hb.range; omega, rfl, _, hb.skipTransfer, rfl⟩

include hb in
private theorem jump (ρ : Nat → M) (w x y : M) :
    programStep (state input ρ ((base + 7 : Nat) : M) w x y) (state input ρ (base : M) w x y) :=
  ⟨base + 7, by have := hb.range; omega, rfl, _, hb.loop, rfl⟩

include hb in
private theorem transfer (ρ : Nat → M) (w x y : M) :
    nativeReaches (state input ρ ((base + 4 : Nat) : M) w x y)
      (state input ρ ((base + 7 : Nat) : M) w (x + y) 0) := by
  let frame := fun i => if i = input.val then w else ρ i
  have reached := NativeTransfer.native_transfer hb.transfer frame y x
  change nativeReaches _ _ at reached
  convert reached using 1 <;> simp only [state, NativeTransfer.transferState] <;> congr 1 <;> funext j <;>
    by_cases hx : j.val = 8 <;> by_cases hy : j.val = 5 <;>
      simp_all [state, registers, NativeTransfer.transferState, frame, Fin.ext_iff,
        Ne.symm hb.input_ne_x, Ne.symm hb.input_ne_y]

include hb in
private theorem round_positive (ρ : Nat → M) (w x y : M) :
    nativeReaches (state input ρ (base : M) (w + 1) (x + 1) y)
      (state input ρ (base : M) w x (y + 1)) :=
  nativeReaches_trans (nativeReaches_step (countdown_step hb ρ w (x + 1) y)) <|
  nativeReaches_trans (nativeReaches_step (advance_y hb ρ w (x + 1) y)) <|
  nativeReaches_trans (nativeReaches_step (test_positive hb ρ w x (y + 1))) <|
  nativeReaches_trans (nativeReaches_step (skip hb ρ w x (y + 1)))
    (nativeReaches_step (jump hb ρ w x (y + 1)))

include hb in
private theorem round_zero (ρ : Nat → M) (w y : M) :
    nativeReaches (state input ρ (base : M) (w + 1) 0 y)
      (state input ρ (base : M) w (y + 1) 0) := by
  have moved := transfer hb ρ w 0 (y + 1)
  rw [zero_add] at moved
  exact nativeReaches_trans (nativeReaches_step (countdown_step hb ρ w 0 y)) <|
    nativeReaches_trans (nativeReaches_step (advance_y hb ρ w 0 y)) <|
    nativeReaches_trans (nativeReaches_step (test_zero hb ρ w (y + 1))) <|
    nativeReaches_trans moved (nativeReaches_step (jump hb ρ w (y + 1) 0))

private def fieldTerm (input j : Fin 9) : ArithmeticSemiterm Nat 5 :=
  if j.val = input.val then #2 else if j.val = 8 then #3 else if j.val = 5 then #4
  else Semiterm.fvar j.val

private def cfgGraph (input : Fin 9) : ArithmeticSemiformula Nat 5 :=
  Rew.bind (fun i : Fin 11 => Fin.cases #0 (fun i => Fin.cases #1 (fieldTerm input) i) i)
    Empty.elim ▹ stateGraph

private theorem cfgGraph_eval (input : Fin 9) (ρ : Nat → M) (code pc w x y : M) :
    (cfgGraph input).Eval ![code,pc,w,x,y] ρ ↔ code = stateCode (state input ρ pc w x y) := by
  have field (j : Fin 9) :
      Semiterm.val ![code,pc,w,x,y] ρ (fieldTerm input j) = registers input ρ w x y j := by
    by_cases hw : j.val = input.val <;> by_cases hx : j.val = 8 <;> by_cases hy : j.val = 5 <;>
      simp_all [fieldTerm, registers]
  have args : Semiterm.val ![code,pc,w,x,y] ρ ∘
      (fun i : Fin 11 => Fin.cases #0 (fun i => Fin.cases #1 (fieldTerm input) i) i) =
      code :> pc :> registers input ρ w x y := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl field j) i
  let r := registers input ρ w x y
  have vector : r = ![r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8] := by
    funext j
    refine Fin.cases rfl (fun j => ?_) j
    repeat first | refine Fin.cases rfl (fun j => ?_) j | exact Fin.elim0 j
  simp only [cfgGraph, Semiformula.eval_rew, Rew.bind_bvar, Rew.bind_fvar, Function.comp_def] at *
  rw [args]
  change stateGraph.Eval (code :> pc :> r) _ ↔ code = stateCode ⟨pc,r⟩
  simpa only [← vector, Empty.eq_elim] using
    (stateGraph_eval code pc (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8))

private def terminates (base : Nat) (input : Fin 9) (ρ : Nat → M) (n : M) : Prop :=
  ∀ x y : M, nativeReaches (state input ρ (base : M) n x y)
    (state input ρ ((base + 8 : Nat) : M) 0
      (modelUnpairLeft (n + modelCantor x y)) (modelUnpairRight (n + modelCantor x y)))

private noncomputable def loopFormula (base : Nat) (input : Fin 9) : ArithmeticSemiformula Nat 1 :=
 “n. ∀x, ∀y, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
  !(cfgGraph input) head ↑base n x y) →
 ∃out, ∃last, ∃p, ∃a, ∃b,
 !nativeRunFormula initial out ∧ !listHeadGraph last out ∧ !exactCantorGraph p x y ∧
 !unpairLeftGraph a (n+p) ∧ !unpairRightGraph b (n+p) ∧
 !(cfgGraph input) last ↑(base+8) 0 a b”

private theorem loopFormula_eval (base : Nat) (input : Fin 9) (ρ : Nat → M) (n : M) :
    (loopFormula base input).Eval ![n] ρ ↔ terminates base input ρ n := by
  have hc (z a b : M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z = modelCantor a b :=
    graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
  have hl (z a : M) : unpairLeftGraph.val.Evalb ![z,a] ↔ z = modelUnpairLeft a :=
    graphValue_spec unpairLeftGraph unpairLeftGraph_total z ![a]
  have hr (z a : M) : unpairRightGraph.val.Evalb ![z,a] ↔ z = modelUnpairRight a :=
    graphValue_spec unpairRightGraph unpairRightGraph_total z ![a]
  simp [loopFormula, terminates, nativeReaches, Semiformula.eval_rew, Function.comp_def,
    Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton, Empty.eq_elim, nativeRunFormula_eval,
    ruleHead_defined.iff, cfgGraph_eval, numeral_eq_natCast, hc, hl, hr]

private noncomputable def certificate (base : Nat) (input : Fin 9) (ρ : Nat → M) :
    FormulaCertificate ρ 1 (fun v => terminates base input ρ (v 0)) :=
  ⟨loopFormula base input, fun v => by
    rw [Matrix.fun_eq_vec_one v]
    exact (loopFormula_eval base input ρ _).symm⟩

include hb in
private theorem loop_terminates (ρ : Nat → M) : ∀ n : M, terminates base input ρ n := by
  apply (certificate base input ρ).induction
  · change terminates base input ρ 0
    intro x y
    simpa only [zero_add, modelUnpairLeft_pair, modelUnpairRight_pair] using
      nativeReaches_step (countdown_zero hb ρ x y)
  · intro n ih
    change terminates base input ρ n at ih
    change terminates base input ρ (n + 1)
    intro x y
    rcases eq_or_ne x 0 with rfl | hx
    · have h : n + modelCantor (y+1) 0 = n+1 + modelCantor 0 y := by
        rw [modelCantor_next_axis]
        ac_rfl
      have rest := ih (y+1) 0
      rw [h] at rest
      exact nativeReaches_trans (round_zero hb ρ n y) rest
    · obtain ⟨x, rfl⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr hx)
      have h : n + modelCantor x (y+1) = n+1 + modelCantor (x+1) y := by
        rw [modelCantor_next_diagonal]
        ac_rfl
      have rest := ih x (y+1)
      rw [h] at rest
      exact nativeReaches_trans (round_positive hb ρ n x y) rest

include hb in
/-- Return the right coordinate to the input register, leaving the left coordinate in register 8. -/
theorem unpair_to_input (restore : NativeTransfer.Bound (base+8) 5 input) (ρ : Nat → M) (n : M) :
    nativeReaches (state input ρ (base : M) n 0 0)
      (state input ρ ((base+11 : Nat) : M) (modelUnpairRight n) (modelUnpairLeft n) 0) := by
  have body := loop_terminates hb ρ n 0 0
  rw [modelCantor_zero, add_zero] at body
  apply nativeReaches_trans body
  let x := modelUnpairLeft n
  let y := modelUnpairRight n
  let frame := fun i => if i = 8 then x else ρ i
  have restored := NativeTransfer.native_transfer restore frame y 0
  change nativeReaches _ _ at restored
  rw [zero_add] at restored
  convert restored using 1 <;> simp only [state, NativeTransfer.transferState] <;> congr 1 <;> funext j <;>
    by_cases hx : j.val = 8 <;> by_cases hy : j.val = 5 <;>
      simp_all [state, registers, NativeTransfer.transferState, frame, x, y, Fin.ext_iff,
        Ne.symm hb.input_ne_x, Ne.symm hb.input_ne_y]

/-- The accumulator register is preserved by the loop and updated by the final transfer. -/
def withAccumulator (dest : Fin 9) (ρ : Nat → M) (h : M) : Nat → M :=
  fun i => if i = dest.val then h else ρ i

include hb in
theorem unpair_add {dest : Fin 9} (dest_ne_input : dest.val ≠ input.val) (dest_ne_y : dest.val ≠ 5)
    (restoreY : NativeTransfer.Bound (base+8) 5 input)
    (restoreX : NativeTransfer.Bound (base+11) 8 dest) (ρ : Nat → M) (n h : M) :
    nativeReaches (state input (withAccumulator dest ρ h) (base : M) n 0 0)
      (state input (withAccumulator dest ρ (h + modelUnpairLeft n)) ((base+14 : Nat) : M)
        (modelUnpairRight n) 0 0) := by
  apply nativeReaches_trans (unpair_to_input hb restoreY (withAccumulator dest ρ h) n)
  let x := modelUnpairLeft n
  let y := modelUnpairRight n
  let frame := fun i => if i = input.val then y else if i = 5 then 0 else ρ i
  have dest_ne_x : dest.val ≠ 8 := by
    intro he
    exact restoreX.distinct (Fin.ext he.symm)
  have restored := NativeTransfer.native_transfer restoreX frame x h
  change nativeReaches _ _ at restored
  have input_ne_x := hb.input_ne_x
  have input_ne_y := hb.input_ne_y
  convert restored using 1 <;> simp only [state, NativeTransfer.transferState] <;> congr 1 <;> funext i
  all_goals
    by_cases hi : i.val = input.val <;> by_cases hy : i.val = 5 <;> by_cases hx : i.val = 8
    all_goals
      first
      | omega
      | simp [registers, frame, x, y, withAccumulator, Fin.ext_iff, hi, hy, hx,
          input_ne_x, input_ne_y, Ne.symm input_ne_x, Ne.symm input_ne_y,
          Ne.symm dest_ne_input, Ne.symm dest_ne_y, Ne.symm dest_ne_x]

end ZF192Support.NativeUnpair
