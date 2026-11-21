module
public import I0451.LeafSemantics
public import I0451.Boundary

/-! Transfer of structured program executions to the literal machine's
interpreter. Branch composition uses the proved carry and jump laws. -/
@[expose] public section
namespace I0451.Runtime

structure Implements (start : RegisterFrame) (signal : Signal)
    (rev : List Bool) (registers : Registers) : Prop where
  halts : signal = .halt → MacroHalts start
  advances : signal ≠ .halt →
    ∃ (n : Nat) (finish : RegisterFrame) (address : Nat), 0 < n ∧
      runMacros n start = some finish ∧ returnAddress signal rev = some address ∧
      RepresentsFrame finish address registers

private theorem LeafResult.implements {f : RegisterFrame} {sig : Signal} {rev : List Bool}
    {regs : Registers} (valid : Permanent f)
    (leaf : LeafResult (macroStep f) sig (returnAddress sig rev) regs) :
    Implements f sig rev regs := by
  constructor
  · intro halt
    subst sig
    exact ⟨0, f, rfl, leaf⟩
  · intro notHalt
    have next : ∃ after, macroStep f = .next after ∧
        returnAddress sig rev = some (pack after.word 0) ∧
        after.regs = tapeRegisters regs := by
      cases sig with
      | normal => exact leaf
      | «break» n => exact leaf
      | restart n => exact leaf
      | halt => exact (notHalt rfl).elim
    obtain ⟨after, command, address, values⟩ := next
    refine ⟨1, after, pack after.word 0, by decide, ?_, address, ?_⟩
    · simp only [runMacros, command]
    · have safe := macroStep_preserves valid
      rw [command] at safe
      exact ⟨safe, rfl, values⟩

private theorem Implements.prepend {f g : RegisterFrame} {n : Nat} {sig : Signal}
    {rev : List Bool} {regs : Registers} (before : runMacros n f = some g)
    (continued : Implements g sig rev regs) : Implements f sig rev regs := by
  constructor
  · intro halt
    obtain ⟨m, last, reach, stop⟩ := continued.halts halt
    exact ⟨n + m, last, runMacros_join before reach rfl, stop⟩
  · intro notHalt
    obtain ⟨m, last, address, positive, reach, addr, view⟩ := continued.advances notHalt
    exact ⟨n + m, last, address, by omega, runMacros_join before reach rfl, addr, view⟩

private theorem Implements.retarget {f : RegisterFrame} {sig outer : Signal} {rev moved : List Bool}
    {regs : Registers} (source : Implements f sig rev regs)
    (halt : sig = .halt ↔ outer = .halt)
    (address : returnAddress sig rev = returnAddress outer moved) :
    Implements f outer moved regs := by
  refine ⟨fun stop => source.halts (halt.2 stop), ?_⟩
  intro notHalt
  rw [← address]
  exact source.advances (fun stop => notHalt (halt.1 stop))

theorem Signal.left_halt {sig result : Signal} (step : sig.leftExit = some result) :
    sig = .halt ↔ result = .halt := by
  cases sig with
  | normal => contradiction
  | «break» n =>
    cases n <;> simp only [Signal.leftExit, Option.some.injEq] at step <;> subst result <;> simp
  | restart n => simp_all [Signal.leftExit]
  | halt => simp_all [Signal.leftExit]

theorem Signal.right_halt {sig result : Signal} (step : sig.rightExit = some result) :
    sig = .halt ↔ result = .halt := by
  cases sig with
  | normal => simp_all [Signal.rightExit]
  | «break» n => simp_all [Signal.rightExit]
  | restart n =>
    cases n
    · contradiction
    · simp only [Signal.rightExit, Option.some.injEq] at step
      subst result
      simp
  | halt => simp_all [Signal.rightExit]

private theorem left_frame {f : RegisterFrame} {word : List Bool} {regs : Registers}
    (view : RepresentsFrame f (pack word 0) regs) :
    RepresentsFrame f (pack (word ++ [false]) 0) regs := by
  have blank : pack (word ++ [false]) 0 = pack word 0 := by
    rw [pack_append]
    rfl
  rw [blank]
  exact view

private theorem to_right {f : RegisterFrame} {word : List Bool} {regs : Registers}
    (fromLeft : Implements f .normal (word ++ [false]).reverse regs) :
    ∃ n g, runMacros n f = some g ∧ RepresentsFrame g (pack (word ++ [true]) 0) regs := by
  obtain ⟨n, g, address, _, reach, points, view⟩ := fromLeft.advances (by decide)
  rw [List.reverse_append] at points
  have equivalent := Option.some.inj ((return_normal_left word.reverse).symm.trans points)
  simp only [List.reverse_reverse] at equivalent
  exact ⟨n, g, reach, equivalent.symm ▸ view⟩

private theorem to_same {f : RegisterFrame} {word : List Bool} {regs : Registers}
    (fromRight : Implements f (.restart 0) (word ++ [true]).reverse regs) :
    ∃ n g, runMacros n f = some g ∧ RepresentsFrame g (pack word 0) regs := by
  obtain ⟨n, g, address, _, reach, points, view⟩ := fromRight.advances (by decide)
  rw [List.reverse_append] at points
  have equivalent := Option.some.inj ((return_restart_right word.reverse).symm.trans points)
  simp only [List.reverse_reverse] at equivalent
  exact ⟨n, g, reach, equivalent.symm ▸ view⟩

theorem Executes.implements {edge : Edge} {input output : Registers} {sig : Signal}
    (execution : Executes edge input sig output) {word : List Bool} {f : RegisterFrame}
    (path : AtEdge word edge) (view : RepresentsFrame f (pack word 0) input) :
    Implements f sig word.reverse output := by
  induction execution generalizing f word with
  | inc index regs => exact (leaf_inc view path).implements view.good
  | decPositive index regs value positive =>
    exact (leaf_dec_pos view path positive).implements view.good
  | decZero index regs zero => exact (leaf_dec_zero view path zero).implements view.good
  | «break» depth regs => exact (leaf_break view path).implements view.good
  | restart depth regs => exact (leaf_restart view path).implements view.good
  | halt regs =>
    have leaf : LeafResult (macroStep f) .halt (returnAddress .halt word.reverse) regs :=
      leaf_halt view path
    exact leaf.implements view.good
  | leftExit left run first ih =>
    have runLeft := ih (path.step left) (left_frame view)
    refine runLeft.retarget (Signal.left_halt first) ?_
    simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append, List.nil_append] using return_left first word.reverse
  | rightExit left right runLeft runRight ret ihLeft ihRight =>
    obtain ⟨n, mid, reach, middle⟩ := to_right (ihLeft (path.step left) (left_frame view))
    have last := ihRight (path.step right) middle
    apply Implements.prepend reach
    refine last.retarget (Signal.right_halt ret) ?_
    simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append, List.nil_append] using return_right ret word.reverse
  | «repeat» left right runLeft runRight again ihLeft ihRight ihAgain =>
    obtain ⟨n, mid, reach, middle⟩ := to_right (ihLeft (path.step left) (left_frame view))
    obtain ⟨m, back, runBack, backView⟩ := to_same (ihRight (path.step right) middle)
    exact Implements.prepend reach (Implements.prepend runBack (ihAgain path backView))

theorem Executes.implements_main {input output : Registers} {sig : Signal}
    (execution : Executes mainEdge input sig output) {f : RegisterFrame}
    (view : RepresentsFrame f 0 input) : Implements f sig [] output :=
  execution.implements (word := []) rfl view

end I0451.Runtime
