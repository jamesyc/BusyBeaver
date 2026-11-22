module
public import ZF192.Simulation.Standard.FrameEncoding
public import ZF192.Simulation.Frames.Coverage
public import ZF192.Simulation.Forward.Startup
public import ZF192Support.Execution.Registers.Scheduler.Soundness
public import ZF192Support.Machine.RegisterProgram.Initial
@[expose] public section
/-! # Standard halting and the checked source program

Unconditional source jumps preserve the aligned frame. A finite jump prefix
ends at an arithmetic or halt instruction, which yields positive progress. -/
namespace M192.Source
open RegisterMachine.Source M192.Calibration
open BinaryTape M192.Control ZF192.BinaryTape ZF192.NativePhysicalLift
open RegisterMachine.SourceSimulation
open scoped FFL.FirstOrder.Arithmetic

/-! ## From the standard model to external runs -/

def Normal (c : Conf) : Prop := BinaryTape.trim c.l = c.l ∧ BinaryTape.trim c.r = c.r

theorem zc_normal (q : Nat) (l r : List Bool) : Normal (zc q l r) :=
  ⟨BinaryTape.trim_trim l, BinaryTape.trim_trim r⟩

theorem step_normal {c d : Conf} (h : step literal c = some d) : Normal d := by
  unfold step at h
  split at h
  · simp at h
  · cases h; exact zc_normal _ _ _
  · cases h; exact zc_normal _ _ _

theorem reach_normal {c d : Conf} (hc : Normal c) (h : Reach literal c d) : Normal d := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing c with
  | zero => cases hk; exact hc
  | succ k ih =>
    simp only [run] at hk
    split at hk
    · simp at hk
    · rename_i c1 h1
      exact ih (step_normal h1) hk

theorem bitsCode_trim_inj : ∀ {a b : List Bool}, bitsCode (M := Nat) a = bitsCode b →
    BinaryTape.trim a = BinaryTape.trim b
  | [], [], _ => rfl
  | [], b :: bs, h => by
    have hb : bitsCode (M := Nat) (b :: bs) = 0 := h.symm
    simp [bitsCode, bitValue] at hb
    obtain ⟨hb1, hbs⟩ := hb
    have := @bitsCode_trim_inj [] bs (by simpa [bitsCode] using hbs.symm)
    simp [BinaryTape.trim, hb1, ← this]
  | a :: as, [], h => by
    have ha : bitsCode (M := Nat) (a :: as) = 0 := h
    simp [bitsCode, bitValue] at ha
    obtain ⟨ha1, has⟩ := ha
    have := @bitsCode_trim_inj as [] (by simpa [bitsCode] using has)
    simp [BinaryTape.trim, ha1, this]
  | a :: as, b :: bs, h => by
    simp only [bitsCode] at h
    have hab : bitValue (M := Nat) a = bitValue b ∧ bitsCode (M := Nat) as = bitsCode bs := by
      cases a <;> cases b <;> simp [bitValue] at h ⊢ <;> omega
    have h1 : a = b := by cases a <;> cases b <;> simp [bitValue] at hab ⊢
    subst h1
    have := bitsCode_trim_inj hab.2
    simp [BinaryTape.trim_cons, this]

theorem encode_inj {c d : Conf} (hc : Normal c) (hd : Normal d)
    (h : encode (M := Nat) c = encode d) : c = d := by
  obtain ⟨q, l, r⟩ := c
  obtain ⟨q', l', r'⟩ := d
  have hq := congrArg State.q h
  have hl : bitsCode (M := Nat) l = bitsCode l' := congrArg State.left h
  have hr : bitsCode (M := Nat) r = bitsCode r' := congrArg State.right h
  simp only [encode] at hq
  have hq' : q = q' := by simpa using hq
  subst hq'
  have hl' := bitsCode_trim_inj hl
  have hr' := bitsCode_trim_inj hr
  simp only [Normal] at hc hd
  rw [hc.1, hd.1] at hl'; rw [hc.2, hd.2] at hr'
  subst hl'; subst hr'; rfl

theorem reach_of_model {c d : Conf} (hc : Normal c) (hd : Normal d)
    (h : Reaches (M := Nat) (encode c) (encode d)) : Reach literal c d := by
  obtain ⟨out, ho, he⟩ := h _ _ (runHistory_singleton _) (ZFR.ArithmeticRepresentation.modelListHead_cons _ _)
  obtain ⟨c', hr, hc'⟩ := nat_history_reach c out ho
  have : c' = d := encode_inj (reach_normal hc hr) hd (stateCode_injective (hc'.symm.trans he))
  exact this ▸ hr

private theorem encode_frame_nat (pc : Nat) (regs : Fin 9 → Nat) (n : Nat) (ρ : List Bool) :
    encode (M:=Nat) (frameN pc regs n ρ) = nativeFrame pc regs n (bitsCode ρ) := by
  simpa using encode_frameN (M:=Nat) pc regs n ρ

private theorem reach1_of_model {c d : Conf} (hd : Normal d)
    (h : Reaches1 (M:=Nat) (encode c) (encode d)) : Reach1 literal c d := by
  obtain ⟨next, first, rest⟩ := h
  obtain ⟨mid, step, he⟩ := (literalStep_encoded_iff c next).mp first
  rw [he] at rest
  exact (Reach1.of_step step).trans_reach (reach_of_model (step_normal step) hd rest)

def sourceFrame (s : ScalarState) (n : Nat) (ρ : List Bool) : Conf :=
  frameN (align s.pc) (permute s.registers) n ρ

private theorem encode_sourceFrame (s : ScalarState) (n : Nat) (ρ : List Bool) :
    encode (M := Nat) (sourceFrame s n ρ) =
    nativeFrame (align s.pc) (permute s.registers) n (bitsCode ρ) :=
  encode_frame_nat _ _ _ _

private theorem halt_of_execute_none {code : Instruction} {s : ScalarState}
    (h : scalarExecute code s = none) : code = .halt := by
  cases code with
  | inc _ _ => simp [scalarExecute] at h
  | dec r _ _ =>
    by_cases hz : s.registers (registerIndex r) = 0 <;> simp [scalarExecute, hz] at h
  | jump _ => simp [scalarExecute] at h
  | halt => rfl

def StandardMove (code : Instruction) (a b : Conf) : Prop :=
  if isJump code then b = a else Reach1 literal a b

theorem site_step (s : ScalarState) (bounded : s.pc < 4341) {code : Instruction}
    (row : compilerProgram s.pc = some code) (n : Nat) (ρ : List Bool) :
    match scalarExecute code s with
    | none => Halts literal (sourceFrame s n ρ)
    | some t => t.pc < 4341 ∧ ∃ n', StandardMove code (sourceFrame s n ρ) (sourceFrame t n' ρ) := by
  cases h : scalarExecute code s with
  | none =>
    have isHalt := halt_of_execute_none h
    subst code
    obtain ⟨terminal, run, stop⟩ := aligned_halt (M := Nat) bounded row s.registers n (bitsCode ρ)
    rw [← encode_sourceFrame s n ρ] at run
    obtain ⟨hist, hh, head⟩ := run.reaches _ _ (runHistory_singleton _)
      (ZFR.ArithmeticRepresentation.modelListHead_cons _ _)
    exact nat_halts_of_history _ hist hh (by simpa only [head] using stop)
  | some t =>
    have exec := ZF192Support.NativeSource.execute_nat code s
    rw [h] at exec
    obtain ⟨pc', ht, hp, n', move⟩ :=
      execute_aligned (M := Nat) bounded row s.registers n (bitsCode ρ) _ exec
    have same : t.pc = pc' := by simpa using hp
    rw [← same, ← encode_sourceFrame s n ρ, ← encode_sourceFrame t n' ρ] at move
    refine ⟨same.symm ▸ ht, n', ?_⟩
    cases kind : isJump code with
    | false =>
      simpa [StandardMove, kind, sourceFrame, frameN] using reach1_of_model (zc_normal _ _ _) (move.positive kind)
    | true =>
      have eq : encode (M := Nat) (sourceFrame t n' ρ) = encode (sourceFrame s n ρ) := by
        simpa [AlignedMove, kind] using move
      simpa [StandardMove, kind, sourceFrame, frameN] using encode_inj (zc_normal _ _ _) (zc_normal _ _ _) eq

private theorem jump_prefix {pc dst : Nat} (path : JumpPath compilerProgram pc dst)
    (bound : pc < 4341) (regs : Fin 9 → Nat) :
    dst < 4341 ∧ align pc = align dst ∧
      (¬ Terminates (scalarNext compilerProgram) ⟨pc, regs⟩ →
       ¬ Terminates (scalarNext compilerProgram) ⟨dst, regs⟩) := by
  induction path with
  | refl pc => exact ⟨bound, rfl, id⟩
  | @step pc mid final row tail ih =>
    obtain ⟨_, _, code, codeRow, valid, matchRow⟩ := checked (checked_at pc bound)
    have hc : code = .jump mid := Option.some.inj (codeRow.symm.trans row)
    subst code
    have next : scalarNext compilerProgram ⟨pc, regs⟩ = some ⟨mid, regs⟩ := by
      simp [scalarNext, row, scalarExecute]
    obtain ⟨fin, same, transfer⟩ := ih valid
    exact ⟨fin, matchRow.trans same, fun no => transfer (fun yes => no (.more next yes))⟩

theorem terminates_halts {s : ScalarState} (h : Terminates (scalarNext compilerProgram) s) :
    s.pc < 4341 → ∀ n ρ, Halts literal (sourceFrame s n ρ) := by
  induction h with
  | @done s endRun =>
    intro hs n ρ
    obtain ⟨_, _, op, row, _, _⟩ := checked (checked_at s.pc hs)
    have hnone : scalarExecute op s = none := by
      simpa [scalarNext, row] using endRun
    have step := site_step s hs row n ρ
    rw [hnone] at step
    exact step
  | @more s t next _ ih =>
    intro hs n ρ
    obtain ⟨_, _, op, row, _, _⟩ := checked (checked_at s.pc hs)
    have exec : scalarExecute op s = some t := by simpa [scalarNext, row] using next
    have facts := site_step s hs row n ρ
    rw [exec] at facts
    obtain ⟨ht, n', move⟩ := facts
    have halt := ih ht n' ρ
    unfold StandardMove at move
    split at move
    · rwa [move] at halt
    · exact halt.of_reach move.reach

theorem halts_terminates {s : ScalarState} (hs : s.pc < 4341) (n : Nat) (ρ : List Bool)
    (h : Halts literal (sourceFrame s n ρ)) : Terminates (scalarNext compilerProgram) s := by
  classical
  by_contra not_done
  let Inv : Conf → Prop := fun c => ∃ t : ScalarState, t.pc < 4341 ∧
    ¬ Terminates (scalarNext compilerProgram) t ∧ ∃ n, c = sourceFrame t n ρ
  refine RegisterMachine.SourceSimulation.not_halts_of_positive_invariant literal Inv ?_ _
    ⟨s, hs, not_done, n, rfl⟩ h
  rintro c ⟨t, ht, hn, n', rfl⟩
  obtain ⟨⟨pc, found⟩, _, _⟩ := checked (checked_at t.pc ht)
  obtain ⟨jumps, op, row, active⟩ := skip_sound found
  obtain ⟨pcBound, same, keep⟩ := jump_prefix jumps ht t.registers
  let u : ScalarState := ⟨pc, t.registers⟩
  have not_end : ¬ Terminates (scalarNext compilerProgram) u := keep (by cases t; exact hn)
  have eq : sourceFrame t n' ρ = sourceFrame u n' ρ := by
    simp [sourceFrame, u, same]
  cases exec : scalarExecute op u with
  | none => exact False.elim (not_end (.done (by simpa [scalarNext, u, row] using exec)))
  | some v =>
    have facts := site_step u pcBound row n' ρ
    rw [exec] at facts
    obtain ⟨hv, n'', moved⟩ := facts
    have move : Reach1 literal (sourceFrame u n' ρ) (sourceFrame v n'' ρ) := by
      simpa [StandardMove, active] using moved
    have next : scalarNext compilerProgram u = some v := by simpa [scalarNext, u, row] using exec
    exact ⟨_, eq.symm ▸ move, v, hv, (fun endRun => not_end (.more next endRun)), n'', rfl⟩

private theorem initial_frame_eq :
    sourceFrame (ZF192Support.NativeCommands.scalar (ZF192Support.NativeCommands.nativeInitial (M := Nat)))
      Startup.startupPadding Startup.rightTail =
    frameN sourceStart.pc sourceStart.registers Startup.startupPadding Startup.rightTail := by
  change frameN (align 25) (permute (ZF192Support.NativeCommands.nativeInitial (M := Nat)).registers) _ _ = _
  rw [startup_pc_eq, startup_registers_eq]
  simp

/-- Exact blank halting is equivalent to termination of the verified source
search. The contextual control bridge is checked inside Lean. -/
theorem blank_halts_iff_nine_register_cfg :
    Halts literal (zc 0 [] []) ↔ Terminates (scalarNext compilerProgram)
      (ZF192Support.NativeCommands.scalar (ZF192Support.NativeCommands.nativeInitial (M := Nat))) := by
  have reach := Startup.blank_to_frame
  rw [← initial_frame_eq] at reach
  constructor
  · intro h
    exact halts_terminates (by decide) Startup.startupPadding Startup.rightTail
      (RegisterMachine.SourceSimulation.halt_after_reach reach h)
  · intro h
    exact (terminates_halts h (by decide) Startup.startupPadding Startup.rightTail).of_reach reach

end M192.Source
