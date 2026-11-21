module
public import I0451.ArithmeticLeaf
public import I0451.ProgramExecution
public import I0451.GraphSharing

/-! Control effects for the finite program graph with arithmetic-model
registers. The tape execution supporting an effect can have model-valued
length. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

structure ModelImplements (f : ModelFrame V) (signal : Signal)
    (rev : List Bool) (registers : Fin 9 → V) : Prop where
  halts : signal = .halt → ModelRealizes f.tape .halt
  advances : signal ≠ .halt →
    ∃ after address, ModelReaches literal f.tape after.tape ∧
      returnAddress signal rev = some address ∧ ModelRepresents after address registers

theorem ModelLeafResult.implements {f : ModelFrame V} {sig : Signal} {rev : List Bool}
    {regs : Fin 9 → V} (valid : ModelPermanent f)
    (leaf : ModelLeafResult (modelMacroStep f) sig (returnAddress sig rev) regs) :
    ModelImplements f sig rev regs := by
  have sound := modelMacroStep_sound f
  constructor
  · intro halt
    subst sig
    change modelMacroStep f = .halt at leaf
    exact leaf ▸ sound
  · intro running
    have next : ∃ after, modelMacroStep f = .next after ∧
        returnAddress sig rev = some (pack after.word 0) ∧ after.regs = modelRegisters regs := by
      cases sig with
      | normal => exact leaf
      | «break» n => exact leaf
      | restart n => exact leaf
      | halt => exact (running rfl).elim
    obtain ⟨after, step, address, values⟩ := next
    have preserved := modelMacroStep_preserves valid
    rw [step] at sound preserved
    exact ⟨after, pack after.word 0, sound, address, ⟨preserved, rfl, values⟩⟩

theorem ModelImplements.prepend {f g : ModelFrame V} {sig : Signal}
    {rev : List Bool} {regs : Fin 9 → V} (arrival : ModelReaches literal f.tape g.tape)
    (continued : ModelImplements g sig rev regs) : ModelImplements f sig rev regs := by
  constructor
  · intro halt
    obtain ⟨m, first⟩ := arrival
    obtain ⟨n, last⟩ := continued.halts halt
    exact ⟨m + n, by rw [trace_add, first]; exact last⟩
  · intro running
    obtain ⟨after, address, back, points, view⟩ := continued.advances running
    exact ⟨after, address, arrival.trans back, points, view⟩

private theorem ModelImplements.retarget {f : ModelFrame V} {sig outer : Signal}
    {rev moved : List Bool} {regs : Fin 9 → V}
    (source : ModelImplements f sig rev regs)
    (halt : sig = .halt ↔ outer = .halt)
    (address : returnAddress sig rev = returnAddress outer moved) :
    ModelImplements f outer moved regs := by
  refine ⟨fun stop => source.halts (halt.mpr stop), ?_⟩
  intro running
  rw [← address]
  exact source.advances (fun stop => running (halt.mp stop))

private theorem left_frame {f : ModelFrame V} {word : List Bool} {regs : Fin 9 → V}
    (view : ModelRepresents f (pack word 0) regs) :
    ModelRepresents f (pack (word ++ [false]) 0) regs := by
  have blank : pack (word ++ [false]) 0 = pack word 0 := by
    rw [pack_append]
    rfl
  exact blank.symm ▸ view

private theorem to_right {f : ModelFrame V} {word : List Bool} {regs : Fin 9 → V}
    (fromLeft : ModelImplements f .normal (word ++ [false]).reverse regs) :
    ∃ g, ModelReaches literal f.tape g.tape ∧ ModelRepresents g (pack (word ++ [true]) 0) regs := by
  obtain ⟨g, address, reach, points, view⟩ := fromLeft.advances (by decide)
  rw [List.reverse_append] at points
  have same := Option.some.inj ((return_normal_left word.reverse).symm.trans points)
  simp only [List.reverse_reverse] at same
  exact ⟨g, reach, same.symm ▸ view⟩

private theorem to_same {f : ModelFrame V} {word : List Bool} {regs : Fin 9 → V}
    (fromRight : ModelImplements f (.restart 0) (word ++ [true]).reverse regs) :
    ∃ g, ModelReaches literal f.tape g.tape ∧ ModelRepresents g (pack word 0) regs := by
  obtain ⟨g, address, reach, points, view⟩ := fromRight.advances (by decide)
  rw [List.reverse_append] at points
  have same := Option.some.inj ((return_restart_right word.reverse).symm.trans points)
  simp only [List.reverse_reverse] at same
  exact ⟨g, reach, same.symm ▸ view⟩

/-- An effect applies to every structurally equal occurrence in the
literal instruction graph. Loop proofs replay their induction at the
actual occurrence with the corresponding address. -/
def ModelEffect (edge : Edge) (input : Fin 9 → V) (sig : Signal) (output : Fin 9 → V) : Prop :=
  ∀ (actual : Edge), SameProgram edge actual →
    ∀ (word : List Bool) (f : ModelFrame V), AtEdge word actual →
      ModelRepresents f (pack word 0) input → ModelImplements f sig word.reverse output

namespace ModelEffect

theorem run {edge : Edge} {input output : Fin 9 → V} {sig : Signal}
    (effect : ModelEffect edge input sig output) {word : List Bool} {f : ModelFrame V}
    (path : AtEdge word edge) (view : ModelRepresents f (pack word 0) input) :
    ModelImplements f sig word.reverse output :=
  effect edge (.same _) word f path view

theorem share {edge target : Edge} {input output : Fin 9 → V} {sig : Signal}
    (effect : ModelEffect edge input sig output) (same : SameProgram edge target) :
    ModelEffect target input sig output :=
  fun actual equivalent => effect actual (same.trans equivalent)


theorem inc (i : Fin 9) (regs : Fin 9 → V) :
    ModelEffect (.instruction (.inc i)) regs .normal (putRegister regs i (regs i + 1)) :=
  by
    intro actual same word f path view
    cases same
    exact (model_leaf_inc view path).implements view.good

theorem dec_pos (i : Fin 9) (regs : Fin 9 → V) (value : V) (positive : regs i = value + 1) :
    ModelEffect (.instruction (.dec i)) regs .normal (putRegister regs i value) :=
  by
    intro actual same word f path view
    cases same
    exact (model_leaf_dec_pos view path positive).implements view.good

theorem dec_zero (i : Fin 9) (regs : Fin 9 → V) (zero : regs i = 0) :
    ModelEffect (.instruction (.dec i)) regs (.break 0) regs :=
  by
    intro actual same word f path view
    cases same
    exact (model_leaf_dec_zero view path zero).implements view.good

theorem breakLeaf (depth : Nat) (regs : Fin 9 → V) :
    ModelEffect (.instruction (.break depth)) regs (.break depth) regs :=
  by
    intro actual same word f path view
    cases same
    exact (model_leaf_break view path).implements view.good

theorem restartLeaf (depth : Nat) (regs : Fin 9 → V) :
    ModelEffect (.instruction (.restart depth)) regs (.restart depth) regs :=
  by
    intro actual same word f path view
    cases same
    exact (model_leaf_restart view path).implements view.good

theorem haltLeaf (regs : Fin 9 → V) :
    ModelEffect (.instruction .halt) regs .halt regs :=
  by
    intro actual same word f path view
    cases same
    exact (model_leaf_halt view path).implements view.good

theorem leftExit {cursor : Cursor} {edge : Edge} {input output : Fin 9 → V} {sig result : Signal}
    (left : outgoing cursor false = some edge) (effect : ModelEffect edge input sig output)
    (exit : sig.leftExit = some result) : ModelEffect (.branch cursor) input result output := by
  intro actual same word f path view
  obtain ⟨moved, rfl, children⟩ := same.branch_view
  obtain ⟨_, leftMoved, compatible⟩ := children false _ left
  refine (effect _ compatible (word ++ [false]) f (path.step leftMoved) (left_frame view)).retarget (Signal.left_halt exit) ?_
  simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append, List.nil_append]
    using return_left exit word.reverse

theorem rightExit {cursor : Cursor} {l r : Edge} {input middle output : Fin 9 → V} {sig result : Signal}
    (left : outgoing cursor false = some l) (right : outgoing cursor true = some r)
    (before : ModelEffect l input .normal middle) (after : ModelEffect r middle sig output)
    (exit : sig.rightExit = some result) : ModelEffect (.branch cursor) input result output := by
  intro actual same word f path view
  obtain ⟨moved, rfl, children⟩ := same.branch_view
  obtain ⟨_, leftMoved, compatibleLeft⟩ := children false _ left
  obtain ⟨_, rightMoved, compatibleRight⟩ := children true _ right
  obtain ⟨g, reach, middleView⟩ := to_right
    (before _ compatibleLeft (word ++ [false]) f (path.step leftMoved) (left_frame view))
  refine ((after _ compatibleRight (word ++ [true]) g (path.step rightMoved) middleView).retarget (Signal.right_halt exit) ?_).prepend reach
  simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append, List.nil_append]
    using return_right exit word.reverse

theorem loopOnce {cursor : Cursor} {l r : Edge} {input middle output : Fin 9 → V}
    (left : outgoing cursor false = some l) (right : outgoing cursor true = some r)
    (before : ModelEffect l input .normal middle) (after : ModelEffect r middle (.restart 0) output)
    {word : List Bool} {f : ModelFrame V} (path : AtEdge word (.branch cursor))
    (view : ModelRepresents f (pack word 0) input) :
    ∃ g, ModelReaches literal f.tape g.tape ∧ ModelRepresents g (pack word 0) output := by
  obtain ⟨g, reach, middleView⟩ := to_right (before.run (path.step left) (left_frame view))
  obtain ⟨next, back, nextView⟩ := to_same (after.run (path.step right) middleView)
  exact ⟨next, reach.trans back, nextView⟩

end ModelEffect

end I0451.Arithmetization
