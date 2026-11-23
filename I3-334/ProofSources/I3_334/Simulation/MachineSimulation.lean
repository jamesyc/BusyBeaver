module
public import I3_334.Simulation.ReferenceProgram
public import I3_334.Simulation.LiteralFrame
public import I3_334.Simulation.CompiledProgram
public import I3_334Support.Search.Compiler.Backward
@[expose] public section

namespace PalomarI3334

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell)
open Stock (Frame)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

theorem literal_boot_one {s t : Frame Nat} (clean : Decoder.Clean s.path)
    (count : 13 ≤ s.values.length) (h : Stock.nextBootstrap s = some t) :
    Reaches machine s.code t.code ∧ Decoder.Clean t.path ∧ t.values.length = s.values.length := by
  cases chosen : Decoder.follow 70 Control.root [] (s.path ++ Engine.zeros s.gap) with
  | none => simp [Stock.nextBootstrap, Stock.executeWith, chosen] at h
  | some d =>
    by_cases fits : Stock.armMargin d ≤ d.rest.length
    · have actual := Stock.executeWith_literal s clean count (pad := s.gap)
        (by rw [Arithmetic.natCast_nat]; exact Or.inl rfl) chosen fits
      change Stock.LiteralRealizes s (Stock.modelExecuteWith s s.gap) at actual
      rw [Stock.modelExecuteWith_nat] at actual
      cases out : Stock.executeWith s s.gap with
      | invalid => simp [Stock.nextBootstrap, out] at h
      | halt => simp [Stock.nextBootstrap, out] at h
      | next u =>
        have eq : u = t := by simpa only [Stock.nextBootstrap, out, Option.some.injEq] using h
        subst u
        rw [out] at actual
        exact ⟨actual.1.reach, actual.2.1, actual.2.2.1⟩
    · simp [Stock.nextBootstrap, Stock.executeWith, chosen, fits] at h

theorem literal_bootstrap {n : Nat} {s t : Frame Nat} (clean : Decoder.Clean s.path)
    (count : 13 ≤ s.values.length) (h : Stock.advanceBootstrap n s = some t) :
    Reaches machine s.code t.code ∧ Decoder.Clean t.path ∧ t.values.length = s.values.length := by
  induction n generalizing s with
  | zero =>
    have eq : s = t := Option.some.inj h
    subst t
    exact ⟨Reaches.refl _ _, clean, rfl⟩
  | succ n ih =>
    cases first : Stock.nextBootstrap s with
    | none => simp [Stock.advanceBootstrap, first] at h
    | some u =>
      obtain ⟨advance, valid, len⟩ := literal_boot_one clean count first
      have rest : Stock.advanceBootstrap n u = some t := by
        simpa only [Stock.advanceBootstrap, first, Option.bind_some] using h
      obtain ⟨run, good, same⟩ := ih valid (len.symm ▸ count) rest
      exact ⟨advance.trans run, good, same.trans len⟩

theorem literal_prepared_boot :
    ∃ time, run machine time blank = some Stock.preparedFrame.config ∧ Stock.preparedFrame.Prepared := by
  have count : 13 ≤ Stock.initialFrame.values.length := by decide +kernel
  obtain ⟨trace, clean, length⟩ := literal_bootstrap Decoder.clean_nil count Stock.bootstrap_exact
  have ready : Stock.preparedFrame.Prepared := by
    refine ⟨clean, length.symm ▸ count, ?_⟩
    change (84 : Nat) = Stock.preparedFrame.span ∨ (84 : Nat) < Stock.preparedFrame.span
    exact Or.inl (by decide +kernel)
  have initial : Stock.initialFrame.config = decoderEntry := by decide +kernel
  rw [Frame.code_nat, Frame.code_nat, initial] at trace
  obtain ⟨time, runTo⟩ := reach_of_arithmetic trace (by decide)
  exact ⟨39765+time, join_run literal_startup runTo, ready⟩

theorem executeNat_literal (s : Frame Nat) (ready : s.Prepared) :
    Stock.LiteralRealizes s (Stock.execute s) := by
  have actual := Stock.execute_literal s ready
  change Stock.LiteralRealizes s (Stock.modelExecuteWith s (Stock.frameCapacity - s.path.length)) at actual
  rw [Stock.modelExecuteWith_nat] at actual
  exact actual

theorem literalSimulation :
    RunSimulation nextFrame machine (fun (s : Frame Nat) c => s.Prepared ∧ c = s.config) := by
  constructor
  · intro s c frame noMore
    obtain ⟨ready, rfl⟩ := frame
    have actual := executeNat_literal s ready
    cases output : Stock.execute s with
    | invalid => rw [output] at actual; exact actual.elim
    | next t => simp [nextFrame, output] at noMore
    | halt =>
      rw [output] at actual
      obtain ⟨left, right, n, path⟩ := actual
      rw [Frame.code_nat, clock_nat] at path
      have stop : (totalRun machine n s.config).state = 334 := by
        have labels := congrArg (fun x : Nat => π₁ x) path
        simpa only [encodeLiteral, cell, encode, Arithmetic.pi₁_pair,
          Arithmetic.natCast_nat, ofNat_nat] using labels
      exact (halts_iff_totalRun _ _).mpr ⟨n, (step_none_iff _ _).mpr (by rw [stop]; decide)⟩
  · intro s t c frame advancing
    obtain ⟨ready, rfl⟩ := frame
    have actual := executeNat_literal s ready
    cases output : Stock.execute s with
    | invalid => simp [nextFrame, output] at advancing
    | halt => simp [nextFrame, output] at advancing
    | next u =>
      have eq : u = t := by simpa only [nextFrame, output, Option.some.injEq] using advancing
      subst u
      rw [output] at actual
      obtain ⟨⟨n, positive, path⟩, clean, sameLength, span⟩ := actual
      rw [Frame.code_nat, Frame.code_nat] at path
      exact ⟨n, t.config, positive, run_of_clock_eq path (by change 16 < 334; decide),
        Stock.prepared_after ready clean sameLength span, rfl⟩

private theorem prepared_program_terminates (ready : Stock.preparedFrame.Prepared) :
    Terminates nextFrame Stock.preparedFrame ↔
      Terminates (Compiler.step referenceProgram) (project Stock.preparedFrame) := by
  apply Terminates.map_iff project Frame.Prepared
  · intro s h
    exact project_step s (by have count := h.2.1; omega)
  · intro s t h advance
    have actual := executeNat_literal s h
    cases out : Stock.execute s with
    | invalid => simp [nextFrame, out] at advance
    | halt => simp [nextFrame, out] at advance
    | next u =>
      have eq : u = t := by simpa only [nextFrame, out, Option.some.injEq] using advance
      subst u
      rw [out] at actual
      exact Stock.prepared_after h actual.2.1 actual.2.2.1 actual.2.2.2
  · exact ready

private theorem boot_projects {s t : Frame Nat} (count : 13 ≤ s.values.length)
    (next : Stock.nextBootstrap s = some t) :
    Compiler.step referenceProgram (project s) = some (project t) := by
  cases found : Decoder.follow 70 Control.root [] (s.path ++ Engine.zeros s.gap) with
  | none => simp [Stock.nextBootstrap, Stock.executeWith, found] at next
  | some d =>
    by_cases margin : Stock.armMargin d ≤ d.rest.length
    · let step := @nextFrameWith Nat instNatCastNat (instOfNatNat 0) (instOfNatNat 1)
        instAddNat instSubNat instDecidableEqNat
      have projected := @project_with Nat instNatCastNat (instOfNatNat 0) (instOfNatNat 1)
        instAddNat instSubNat instDecidableEqNat s (by omega) s.gap d found margin
      change (step s s.gap).map project = _ at projected
      have same : step s s.gap = Stock.nextBootstrap s := by
        unfold step nextFrameWith Stock.nextBootstrap
        cases Stock.executeWith s s.gap <;> rfl
      rw [same, next, Option.map_some] at projected
      exact projected.symm
    · simp [Stock.nextBootstrap, Stock.executeWith, found, margin] at next

theorem bootstrap_program {n : Nat} {s t : Frame Nat} (clean : Decoder.Clean s.path)
    (count : 13 ≤ s.values.length) (h : Stock.advanceBootstrap n s = some t) :
    Terminates (Compiler.step referenceProgram) (project s) ↔
      Terminates (Compiler.step referenceProgram) (project t) := by
  induction n generalizing s with
  | zero =>
    have eq : s = t := Option.some.inj h
    rw [eq]
  | succ n ih =>
    cases first : Stock.nextBootstrap s with
    | none => simp [Stock.advanceBootstrap, first] at h
    | some u =>
      have advance := boot_projects count first
      obtain ⟨_, valid, len⟩ := literal_boot_one clean count first
      have rest : Stock.advanceBootstrap n u = some t := by
        simpa only [Stock.advanceBootstrap, first, Option.bind_some] using h
      refine Iff.trans ?_ (ih valid (len.symm ▸ count) rest)
      refine ⟨?_, fun reaches => .advance advance reaches⟩
      intro reaches
      cases reaches with
      | stop done => rw [advance] at done; contradiction
      | advance done suffix => rw [advance] at done; cases done; exact suffix

theorem reference_closed : referenceProgram.closed := by
  rw [Program.closed, ← normalize_needs referenceProgram, SearchProgram.reference_normalized_eq, normalize_needs]
  decide +kernel

theorem literal_halts_iff_search_program :
    HaltsFrom machine blank ↔ IteratesToHalt SearchProgram.main (fun _ => 0) := by
  have count : 13 ≤ Stock.initialFrame.values.length := by decide +kernel
  have initial : project Stock.initialFrame = atPath [] (fun _ => 0) := by
    have values : ∀ r : Register, storeOf Stock.initialFrame.values r = 0 := by decide +kernel
    change atPath [] (storeOf Stock.initialFrame.values) = _
    rw [funext values]
  have prelude := bootstrap_program Decoder.clean_nil count Stock.bootstrap_exact
  rw [initial] at prelude
  obtain ⟨_, boot, ready⟩ := literal_prepared_boot
  exact (halts_after_run boot).trans ((literalSimulation.halts_iff ⟨ready, rfl⟩).trans
    ((prepared_program_terminates ready).trans
      (prelude.symm.trans ((halts_iff_iterations referenceProgram reference_closed _).trans
        (SearchProgram.reference_matches_source.iterates _)))))

end PalomarI3334
