module
public import I3_334.Simulation.LiteralFrame
public import I3_334.Simulation.ReferenceProgram
public import I3_334Support.Search.Arithmetic.PackedFrame
@[expose] public section

namespace PalomarI3334.ModelFrame

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell registers)
open Stock (Frame frame)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem frame_file_unchanged {s t : Frame M} (outcome : Stock.execute s = .next t) :
    t.values.length = s.values.length ∧
    t.values.take (s.values.length-12) = s.values.take (s.values.length-12) := by
  unfold Stock.execute Stock.executeWith at outcome
  cases found : Decoder.follow 70 Control.root [] (s.path ++ Engine.zeros (Stock.frameCapacity-s.path.length)) with
  | none => simp [found] at outcome
  | some d =>
    by_cases enough : Stock.armMargin d ≤ d.rest.length
    · cases command : d.command with
      | halt => simp [found,enough,Stock.advanceFrame,command] at outcome
      | «break» skip =>
        simp only [found,enough,↓reduceIte,Stock.advanceFrame,command,Stock.Outcome.next.injEq] at outcome
        subst t
        exact ⟨rfl,rfl⟩
      | «continue» skip =>
        simp only [found,enough,↓reduceIte,Stock.advanceFrame,command,Stock.Outcome.next.injEq] at outcome
        subst t
        exact ⟨rfl,rfl⟩
      | register dec r =>
        simp only [found,enough,↓reduceIte,Stock.advanceFrame,command,Stock.Outcome.next.injEq] at outcome
        subst t
        exact ⟨List.length_set, List.take_set_of_le (Nat.sub_le_sub_left (by have h := r.isLt; omega)
          s.values.length)⟩
    · simp [found,enough] at outcome

theorem trim_clean {path : List Bool} (clean : Decoder.Clean path) : Decoder.Clean (trimPC path) := by
  obtain ⟨stem,n,rfl,valid⟩ := clean
  rw [trimPC_zeros]
  obtain ⟨k,padded⟩ := trimPC_padding stem
  have keep : Decoder.ValidPrefix Control.root (trimPC stem) :=
    Decoder.ValidPrefix.initial _ _ _ (padded ▸ valid)
  exact ⟨trimPC stem,0,by simp,keep⟩

theorem frame_trim (s : Frame M) :
    ∃ gap : M, s.code = frame (trimPC s.path) gap s.values ∧
      s.span = ((trimPC s.path).length : M)+gap := by
  obtain ⟨n,padded⟩ := trimPC_padding s.path
  let stem := trimPC s.path
  have pathEq : s.path = stem ++ Engine.zeros n := padded
  refine ⟨s.gap+(n : M),?_,?_⟩
  · unfold Frame.code frame
    have run := congrArg (fun p => packWord p (repeatBit false s.gap (registers s.values 0))) pathEq
    rw [packWord_append, ← repeatBit_cast, ← repeatBit_add] at run
    exact congrArg (cell Control.root 1) run
  · have sizes := congrArg List.length pathEq
    rw [List.length_append,List.length_replicate] at sizes
    change (s.path.length : M)+s.gap = (stem.length : M)+(s.gap+(n : M))
    rw [sizes,Nat.cast_add]
    simp only [add_assoc, add_comm, add_left_comm]

noncomputable def frameOf (stem : List M) (path : List Bool) (gap word : M) : Frame M :=
  ⟨trimPC path, gap, stem ++ (Store.ofCode word).file⟩

theorem frameOf_project (stem : List M) (path : List Bool) (gap word : M) :
    project (frameOf stem path gap word) = atPath path (Store.ofCode word) := by
  simp [frameOf,project,atPath,trimPC_idem,storeOf_file]

/-- A model-finite run followed by a decoded, prepared instruction boundary. -/
def ReachedAt (origin : M) (stem : List M) (path : List Bool) (word : M) : Prop :=
  len word = 12 ∧ Decoder.Clean (trimPC path) ∧
  ∃ gap : M, (84 : M) ≤ ((trimPC path).length : M)+gap ∧
    Reaches machine origin (frameOf stem path gap word).code

theorem reachedAt_definable (origin : M) (stem : List M) (path : List Bool) :
    𝚺ᴬ₁-Predicate (ReachedAt origin stem path) := by
  have code : 𝚺ᴬ₁.DefinableFunction (fun v : Fin 2 → M => (frameOf stem path (v 0) (v 1)).code) :=
    packedFrame_definable₂ Control.root stem path
  have reaches : 𝚺ᴬ₁-Relation (Reaches (M := M) machine) := Reaches.definable _
  have run := reaches.comp (Bounding.HierarchySymbol.DefinableFunction.const origin) code
  have margin : 𝚺ᴬ₁.Definable (fun v : Fin 2 → M => (84 : M) ≤ ((trimPC path).length : M)+v 0) := by
    definability
  have size : 𝚺ᴬ₁-Predicate (fun word : M => len word = 12) := by definability
  change 𝚺ᴬ₁.Definable (fun v : Fin 1 → M => ReachedAt origin stem path (v 0))
  classical
  by_cases clean : Decoder.Clean (trimPC path)
  · simpa only [ReachedAt,clean,true_and] using size.and (margin.and run).exs
  · simp only [ReachedAt,clean,false_and,and_false]
    definability

theorem reachedAt_of_frame {origin : M} (s : Frame M) (ready : s.Prepared)
    (reached : Reaches machine origin s.code) :
    ReachedAt origin (s.values.take (s.values.length-12)) s.path (storeOf s.values).code := by
  obtain ⟨gap,normalized,span⟩ := frame_trim s
  refine ⟨Store.len_code _,trim_clean ready.1,gap,span ▸ ready.2.2,?_⟩
  have file := file_storeOf s.values (by have h := ready.2.1; omega)
  rw [frameOf,Frame.code,Store.ofCode_code,file,List.take_append_drop,← normalized]
  exact reached

theorem frameOf_prepared (stem : List M) (nonempty : 0 < stem.length)
    (path : List Bool) (gap word : M) (clean : Decoder.Clean (trimPC path))
    (margin : (84 : M) ≤ ((trimPC path).length : M)+gap) :
    (frameOf stem path gap word).Prepared := by
  refine ⟨clean,?_,margin⟩
  simp only [frameOf,List.length_append,Store.length_file]
  omega

/-- The same primitive operation chosen by the checked decoder runs at
a standard instruction address in every model of IΣ₁. -/
theorem advance_reachedAt {origin s t : M} {stem : List M} (nonempty : 0 < stem.length)
    {p q : List Bool} (reached : ReachedAt origin stem p s)
    (step : Compiler.step PalomarI3334.referenceProgram (atPath p (Store.ofCode s)) =
      some (atPath q (Store.ofCode t))) (typed : len t = (12 : M)) :
    ReachedAt origin stem q t := by
  obtain ⟨_,clean,gap,margin,reached⟩ := reached
  let input := frameOf stem p gap s
  have ready : input.Prepared := frameOf_prepared stem nonempty p gap s clean margin
  have projects := frameOf_project stem p gap s
  have count : 12 ≤ input.values.length := by have h := ready.2.1; omega
  have simulated := project_step input count
  rw [projects,step] at simulated
  have execution := Stock.execute_literal input ready
  cases out : Stock.execute input with
  | invalid => rw [out] at execution; exact execution.elim
  | halt => simp [nextFrame,out] at simulated
  | next output =>
    have projection : project output = atPath q (Store.ofCode t) := by
      simpa only [nextFrame,out,Option.map_some,Option.some.injEq] using simulated
    rw [out] at execution
    obtain ⟨duration,good,_,outcomeSpan⟩ := execution
    obtain ⟨size,preserved⟩ := frame_file_unchanged out
    have inputSize : input.values.length = stem.length+12 := by
      simp only [input,frameOf,List.length_append,Store.length_file]
    have splitAt : input.values.length-12 = stem.length := by omega
    have retained : output.values.take (output.values.length-12) = stem := by
      rw [splitAt] at preserved
      rw [size,splitAt,preserved]
      change (stem ++ (Store.ofCode s).file).take stem.length = stem
      simp
    have read : storeOf output.values = Store.ofCode t :=
      congrArg PathState.registers projection
    have branch : trimPC output.path = trimPC q := congrArg PathState.pc projection
    have long : 12 ≤ output.values.length := by rw [size,inputSize]; omega
    have file : output.values = stem ++ (Store.ofCode t).file := by
      rw [← read, file_storeOf output.values long, ← retained, List.take_append_drop]
    obtain ⟨newGap,normalized,span⟩ := frame_trim output
    rw [branch,file] at normalized
    refine ⟨typed,branch ▸ trim_clean good,newGap,?_,(reached.trans duration.reach).trans ?_⟩
    · have enough := le_trans ready.2.2 outcomeSpan
      rwa [span,branch] at enough
    · rw [normalized]
      exact Reaches.refl _ _

def ReachesHalt (origin : M) : Prop :=
  ∃ l r : M, Reaches machine origin (cell 334 l r)

theorem halt_reachedAt {origin s : M} {stem : List M} (nonempty : 0 < stem.length)
    {p : List Bool} (reached : ReachedAt origin stem p s)
    (terminal : Compiler.step PalomarI3334.referenceProgram (atPath p (Store.ofCode s)) = none) :
    ReachesHalt origin := by
  obtain ⟨_,clean,gap,margin,reached⟩ := reached
  let input := frameOf stem p gap s
  have ready : input.Prepared := frameOf_prepared stem nonempty p gap s clean margin
  have projects := frameOf_project stem p gap s
  have count : 12 ≤ input.values.length := by have h := ready.2.1; omega
  have sim := project_step input count
  rw [projects,terminal] at sim
  have execution := Stock.execute_literal input ready
  cases out : Stock.execute input with
  | invalid => rw [out] at execution; exact execution.elim
  | next output => simp [nextFrame,out] at sim
  | halt =>
    rw [out] at execution
    obtain ⟨left,right,run⟩ := execution
    exact ⟨left,right,reached.trans run⟩

end PalomarI3334.ModelFrame
