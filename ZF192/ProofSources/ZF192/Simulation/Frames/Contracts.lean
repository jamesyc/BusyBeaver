module
public import ZF192.Simulation.Window
public import ZF192.Simulation.RegisterFile.Macros
public import ZF192.Machine.Decoder.Sites
public import ZF192.Tape.Halting.Terminal
@[expose] public section
/-! # Source frames of ZF192 and the meaning of the site checks

At a source boundary the tape is: the program window of the current address, a padding run
of `n` ones, the gate `00`, the nine register blocks (register `r` of the source program is
block `logical r`), and a blank file exterior; right of the window an arbitrary numeral
`ρ`. `n`, `ρ` and the nine registers are arbitrary elements of the PA model.
`frameImplements_of_check` turns a successful `siteCheck` into the exact physical contract of
that source instruction. -/
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation M192 M192.Window M192.Paths M192.Sites
open RegisterMachine.Source (Instruction instructionBound)
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The nine blocks in tape order: block `j` holds source register `physicalRegister j`. -/
def regList (r:Fin 9→M) : List M := List.ofFn r

noncomputable def incrementRegisters (r:Fin 9→M) (k:Fin 9) : Fin 9→M := fun i=>if i=k then r i+1 else r i
noncomputable def decrementRegisters (r:Fin 9→M) (k:Fin 9) : Fin 9→M :=
 fun i=>if i=k then modelPredecessor (r i) else r i

noncomputable def nativeFrame (pc:Nat) (regs:Fin 9→M) (n ρ:M) : State M :=
 cell root (bitPrefix (winL (fpath pc)) (ones n (2*(2*file (regList regs) 0)))) (bitPrefix (winR (fpath pc)) ρ)

def FrameImplements (pc : Nat) (code : Instruction) : Prop :=
  match code with
  | .inc r k => ∃ hr : r < 9, ∀ (n ρ : M) (regs : Fin 9 → M), ∃ n' : M,
      Reaches1 (nativeFrame pc regs n ρ)
        (nativeFrame k (incrementRegisters regs ⟨r,hr⟩) n' ρ)
  | .dec r z p => ∃ hr : r < 9, ∀ (n ρ : M) (regs : Fin 9 → M),
      (regs ⟨r,hr⟩ = 0 → Reaches1 (nativeFrame pc regs n ρ) (nativeFrame z regs n ρ)) ∧
      (regs ⟨r,hr⟩ ≠ 0 → ∃ n' : M,
        Reaches1 (nativeFrame pc regs n ρ)
          (nativeFrame p (decrementRegisters regs ⟨r,hr⟩) n' ρ))
  | .jump k => ∀ (n ρ : M) (regs : Fin 9 → M),
      Reaches1 (nativeFrame pc regs n ρ) (nativeFrame k regs n ρ)
  | .halt => ∀ (n ρ : M) (regs : Fin 9 → M), ∃ terminal,
      Reaches1 (nativeFrame pc regs n ρ) terminal ∧
      ∀ next, ¬ codedStep (stateCode terminal) next

/-! ## Selected register -/

private theorem regList_update (r : Fin 9 → M) (k : Fin 9) (value : M) :
    regList (fun i => if i = k then value else r i) = (regList r).set k.val value := by
  apply List.ext_getElem
  · simp [regList]
  · intro i hi hj
    simp only [regList, List.getElem_ofFn, List.getElem_set]
    by_cases h : i = k.val
    · subst i
      simp
    · have hn : (⟨i, by simpa [regList] using hi⟩ : Fin 9) ≠ k :=
        fun eq => h (congrArg Fin.val eq)
      simp [h, Ne.symm h, hn]

lemma regList_split (r : Nat) (hr : r < 9) (regs : Fin 9 → M) :
    ∃ pre post : List M,
      pre.length = r ∧ regList regs = pre ++ regs ⟨r, hr⟩ :: post ∧
      regList (incrementRegisters regs ⟨r, hr⟩) = pre ++ (regs ⟨r, hr⟩ + 1) :: post ∧
      ∀ v : M, regs ⟨r, hr⟩ = v + 1 →
        regList (decrementRegisters regs ⟨r, hr⟩) = pre ++ v :: post := by
  let k : Fin 9 := ⟨r, hr⟩
  let rows := regList regs
  have inside : r < rows.length := by simpa [rows, regList] using hr
  refine ⟨rows.take r, rows.drop (r + 1), by simp [List.length_take, Nat.min_eq_left inside.le], ?_, ?_, ?_⟩
  · have h := List.take_append_drop r rows
    rw [List.drop_eq_getElem_cons inside] at h
    simpa only [rows, regList, List.getElem_ofFn] using h.symm
  · change regList (incrementRegisters regs k) = _
    have update : incrementRegisters regs k = (fun i => if i = k then regs k + 1 else regs i) := by
      funext i
      by_cases h : i = k <;> simp [incrementRegisters, h]
    rw [update, regList_update, List.set_eq_take_append_cons_drop, if_pos (show k.val < (regList regs).length from inside)]
  · intro v hv
    change regList (decrementRegisters regs k) = _
    have update : decrementRegisters regs k = (fun i => if i = k then v else regs i) := by
      funext i
      by_cases h : i = k
      · subst i
        simpa only [decrementRegisters, ite_true, show regs k = v + 1 from hv, modelPredecessor_succ]
      · simp [decrementRegisters, h]
    rw [update, regList_update, List.set_eq_take_append_cons_drop, if_pos (show k.val < (regList regs).length from inside)]

/-! ## Crossing the padding run -/

lemma pad_in {q:Nat} (row:M192.literal q true=some (true,false,q)) (n F Y:M) :
 Reaches (cell q (ones n (2*(2*F))) (1+2*Y)) (cell q (2*F) (2*(1+2*ones n Y))) := by
 refine ((by simpa [bitValue] using stepL1 row (ones n (2*(2*F))) Y) :
  Reaches (cell q (ones n (2*(2*F))) (1+2*Y)) (cellL q (ones n (2*(2*F))) (1+2*Y))).trans ?_
 refine (scanL1 row n (2*(2*F)) (1+2*Y)).trans ?_
 rw [cellL_zero,ones_commute,ones_succ]
 exact Reaches.refl _

lemma pad_out {q:Nat} (row:M192.literal q true=some (true,true,q)) (n L Y:M) :
 Reaches (cell q L (1+2*ones n Y)) (cell q (1+2*ones n L) Y) := by
 refine ((by simpa [bitValue] using stepR1 row L (ones n Y)) :
  Reaches (cell q L (1+2*ones n Y)) (cell q (1+2*L) (ones n Y))).trans ?_
 refine (scanR1 row n (1+2*L) Y).trans ?_
 rw [ones_commute,ones_succ]
 exact Reaches.refl _

lemma issue_row {chain:List Nat} (hc:ChainRows chain) (j:Nat) (hj:j+2≤10) :
 M192.literal (chain.getD (j+2) 0) true=some (true,false,chain.getD (j+2) 0) := hc.2 ⟨j+1,by omega⟩

/-! ## Padding, macro, padding -/

lemma inc_middle (pre post:List M) (hp:pre.length+2≤10) (v n Y:M) :
 Reaches (cell (chainI.getD (pre.length+2) 0) (ones n (2*(2*file (pre++v::post) 0))) (1+2*Y))
  (cell readSuccess (1+2*ones (n+1) (2*(2*file (pre++(v+1)::post) 0))) Y) := by
 refine (pad_in (issue_row chainI_rows pre.length hp) n _ Y).trans
   ((inc_macro pre post hp v (ones n Y)).trans ?_)
 have h:=pad_out row_readSuccess_1 n (1+2*(2*(2*file (pre++(v+1)::post) 0))) Y
 rwa [ones_commute] at h

lemma zero_middle (pre post:List M) (hp:pre.length+2≤10) (n Y:M) :
 Reaches (cell (chainD.getD (pre.length+2) 0) (ones n (2*(2*file (pre++0::post) 0))) (1+2*Y))
  (cell readZero (1+2*ones n (2*(2*file (pre++0::post) 0))) Y) :=
 (pad_in (issue_row chainD_rows pre.length hp) n _ Y).trans
  ((dec_zero_macro pre post hp (1+2*ones n Y)).trans (pad_out row_readZero_1 n _ Y))

lemma pos_middle (pre post:List M) (hp:pre.length+2≤10) (v n Y:M) :
 Reaches (cell (chainD.getD (pre.length+2) 0) (ones n (2*(2*file (pre++(v+1)::post) 0))) (1+2*Y))
  (cell readSuccess (1+2*ones (n+1) (2*(2*file (pre++v::post) 0))) Y) := by
 refine (pad_in (issue_row chainD_rows pre.length hp) n _ Y).trans
   ((dec_pos_macro pre post hp v (ones n Y)).trans ?_)
 have h:=pad_out row_readSuccess_1 n (1+2*(2*(2*file (pre++v::post) 0))) Y
 rwa [ones_commute] at h

/-! ## Halting -/

lemma halt_no_step (s:State M) (hq:s.q=(192:Nat)) : ∀next,¬codedStep (stateCode s) next := by
 rintro next ⟨t,u,ht,hu,q,hb,he,rest⟩
 have he':s=t:=stateCode_injective ht
 subst t
 have hn:(192:Nat)=q := Nat.cast_inj.mp (hq.symm.trans he)
 omega

lemma backTo_spec {q k:Nat} {wr:List Bool} (h:backTo q wr k=true) : ∃rest q2,
 wr=true::rest ∧ wrun atRoot fuel q [true] rest=some (q2,winL (fpath k),winR (fpath k)) := by
 unfold backTo at h
 split at h
 · rename_i rest
   split at h
   · rename_i q2 wl2 wr2 hpost
     simp only [frameIs,Bool.and_eq_true,beq_iff_eq] at h
     exact ⟨rest,q2,rfl,by rw [← wrunReturn_eq,hpost,h.1,h.2]⟩
   · simp at h
 · simp at h

/-- Decode a checked return after the arithmetic and padding scans. -/
private lemma return_frame {q k q' : Nat} {rest : List Bool}
    (h : wrun atRoot fuel q [true] rest = some (q', winL (fpath k), winR (fpath k)))
    (n ρ : M) (regs : Fin 9 → M) :
    Reaches (cell q (1+2*ones n (2*(2*file (regList regs) 0))) (bitPrefix rest ρ))
      (nativeFrame k regs n ρ) := by
  obtain ⟨stop, run⟩ := model_wrun (ones n (2*(2*file (regList regs) 0))) ρ fuel q [true] rest h
  simp only [atRoot, Bool.and_eq_true, beq_iff_eq] at stop
  simpa [nativeFrame, stop.1, bitPrefix, bitValue] using run

/-! ## Site contracts -/

theorem frameImplements_of_check (i : Nat) (code : Instruction)
    (row : program i = some code) (checked : siteCheck i = true) :
    instructionBound siteCount code ∧ FrameImplements (M := M) i code := by
  simp only [siteCheck, row, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨checked.1, frame_of_instruction i code checked.1 checked.2⟩
where
  frame_of_instruction (i : Nat) (code : Instruction) (bound : instructionBound siteCount code)
      (h : instructionCheck i code = true) :
      FrameImplements (M:=M) i code := by
    cases code with
    | halt =>
      simp only [instructionCheck, runAddress_eq _ _ rfl, Option.isSome_iff_exists] at h
      obtain ⟨⟨q, wl, wr⟩, hrun⟩ := h
      intro n ρ regs
      obtain ⟨stop, run⟩ :=
        model_wrun1 (ones n (2*(2*file (regList regs) 0))) ρ hrun
      simp only [atHalt, beq_iff_eq] at stop
      exact ⟨_, run, halt_no_step _ (by simp [cell, stop, halt])⟩
    | jump k =>
      simp only [instructionCheck, runAddress_eq _ _ wrunRoot_eq] at h
      split at h
      · rename_i q wl wr hrun
        simp only [frameIs, Bool.and_eq_true, beq_iff_eq] at h
        intro n ρ regs
        obtain ⟨stop, run⟩ :=
          model_wrun1 (ones n (2*(2*file (regList regs) 0))) ρ hrun
        simp only [atRoot, Bool.and_eq_true, beq_iff_eq] at stop
        simpa [nativeFrame, h.1, h.2, stop.1] using run
      · simp at h
    | inc r k =>
      simp only [instructionCheck] at h
      split at h
      · rename_i q wl wr hgate
        rw [toGate_eq] at hgate
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hq, hback⟩ := h
        obtain ⟨rest,q',rfl,hpost⟩ := backTo_spec hback
        have hr : r < 9 := bound.1
        refine ⟨hr, fun n ρ regs => ?_⟩
        obtain ⟨pre,post,hlen,hl,hli,-⟩ := regList_split r hr regs
        have hp : pre.length+2≤10 := by omega
        obtain ⟨stop, entry⟩ :=
          model_wrun1 (ones n (2*(2*file (regList regs) 0))) ρ hgate
        simp only [atGate, List.isEmpty_iff] at stop
        subst wl
        refine ⟨n+1, entry.trans ?_⟩
        simp only [bitPrefix, bitValue, ite_true]
        have hsel : chainI.getD (r+2) 0 = chainI.getD (pre.length+2) 0 := by rw [hlen]
        rw [hl,hq,hsel]
        refine (inc_middle pre post hp (regs ⟨r,hr⟩) n (bitPrefix rest ρ)).trans ?_
        rw [←hli]
        exact return_frame hpost (n+1) ρ _
      · simp at h
    | dec r z k =>
      simp only [instructionCheck] at h
      split at h
      · rename_i q wl wr hgate
        rw [toGate_eq] at hgate
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨hq,hzero⟩,hpos⟩ := h
        obtain ⟨rest,qz,rfl,hpostz⟩ := backTo_spec hzero
        obtain ⟨rest',qp,hrest,hpostp⟩ := backTo_spec hpos
        simp only [List.cons.injEq, true_and] at hrest
        subst rest'
        have hr : r < 9 := bound.1
        refine ⟨hr, fun n ρ regs => ?_⟩
        obtain ⟨pre,post,hlen,hl,-,hld⟩ := regList_split r hr regs
        have hp : pre.length+2≤10 := by omega
        obtain ⟨stop, entry⟩ :=
          model_wrun1 (ones n (2*(2*file (regList regs) 0))) ρ hgate
        simp only [atGate, List.isEmpty_iff] at stop
        subst wl
        simp only [bitPrefix, bitValue, ite_true] at entry
        change Reaches1 (nativeFrame i regs n ρ) _ at entry
        have hsel : chainD.getD (r+2) 0 = chainD.getD (pre.length+2) 0 := by rw [hlen]
        rw [hl,hq,hsel] at entry
        constructor
        · intro hz
          rw [hz] at entry
          refine entry.trans ((zero_middle pre post hp n (bitPrefix rest ρ)).trans ?_)
          have same : pre++(0:M)::post = regList regs := by rw [hl,hz]
          rw [same]
          exact return_frame hpostz n ρ _
        · intro hnz
          obtain ⟨v,hv⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr hnz)
          rw [hv] at entry
          refine ⟨n+1, entry.trans ((pos_middle pre post hp v n (bitPrefix rest ρ)).trans ?_)⟩
          rw [←hld v hv]
          exact return_frame hpostp (n+1) ρ _
      · simp at h

end ZF192.BinaryTape
