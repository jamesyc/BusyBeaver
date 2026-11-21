module
public import I3_380.Search.Arithmetic.FrameNormalForm
@[expose] public section

namespace PalomarI3380.Compiler

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticMachine
open ArithmeticMachine.Reference (Frame frame registers cell ReachesHalt)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def frameFromCode (stem : List M) (path : List Bool) (gap code : M) : Frame M :=
  ⟨trimPC path,gap,stem ++ (Store.ofCode code).file⟩

theorem trimPC_idem (path : List Bool) : trimPC (trimPC path) = trimPC path := by
  obtain ⟨n,eq⟩ := trimPC_padding path
  exact (trimPC_zeros _ _).symm.trans (congrArg trimPC eq.symm)

theorem frameFromCode_project (stem : List M) (path : List Bool) (gap code : M) :
    projectFrame (frameFromCode stem path gap code) = atPath path (Store.ofCode code) := by
  simp [projectFrame,frameFromCode,Frame.logical,project,atPath,trimPC_idem,storeOf_file]

private theorem pushBit_definable (bit : Bool) : 𝚺ᴬ₁-Function₁ (pushBit (M := M) bit) :=
  (show 𝚺ᴬ₁-Function₁ (pushBit (M := M) bit) via pushBitDef bit from
    .mk fun v => by
      rw [Matrix.fun_eq_vec_two v]
      simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,show Fin.succ (0 : Fin 1) = (1 : Fin 2) from rfl] using
        pushBitDef_eval bit (v 0) (v 1)).to_definable

private theorem packWord_definable₁ (path : List Bool) :
    𝚺ᴬ₁-Function₁ (packWord (M := M) path) := by
  induction path with
  | nil =>
    change 𝚺ᴬ₁-Function₁ (fun x : M => x)
    definability
  | cons bit rest ih =>
    have bitDef := pushBit_definable (M := M) bit
    change 𝚺ᴬ₁-Function₁ (fun x : M => pushBit bit (packWord rest x))
    definability

private theorem registerList_definable₁ (fields : List (M → M))
    (definition : ∀ f ∈ fields, 𝚺ᴬ₁-Function₁ f) :
    𝚺ᴬ₁-Function₁ (fun x => registers (fields.map fun value => value x) 0) := by
  induction fields with
  | nil =>
    change 𝚺ᴬ₁-Function₁ (fun _ : M => (0 : M))
    definability
  | cons f rest ih =>
    have first := definition f (List.mem_cons_self ..)
    have tail := ih (fun g entry => definition g (List.mem_cons_of_mem f entry))
    let count := fun x : M => f x+1
    let ending := fun x : M => registers (rest.map fun value => value x) 0
    have counted : 𝚺ᴬ₁-Function₁ count := by unfold count; definability
    have repeated : 𝚺ᴬ₁-Function₁ (fun x : M => repeatBit true (count x) (ending x)) :=
      Bounding.HierarchySymbol.DefinableFunction₂.comp (F := repeatBit true) counted tail
    letI : 𝚺ᴬ₁-Function₁ (pushBit (M := M) false) := pushBit_definable false
    exact Bounding.HierarchySymbol.DefinableFunction₁.comp (F := pushBit false) repeated

private theorem frameRegister_definable₁ (stem : List M) :
    𝚺ᴬ₁-Function₁ (fun code => registers (stem ++ (Store.ofCode code).file) 0) := by
  let fields := stem.map (fun value => fun _ : M => value) ++
    (List.ofFn (fun r : Register => fun code : M => Store.ofCode code r)).reverse
  have every (f : M → M) (entry : f ∈ fields) : 𝚺ᴬ₁-Function₁ f := by
    rcases List.mem_append.mp entry with fixed | logical
    · obtain ⟨constant,_,rfl⟩ := List.mem_map.mp fixed
      definability
    · obtain ⟨r,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp logical)
      exact Store.read_definable r
  have graph := registerList_definable₁ fields every
  have identity : List.map (fun x : M => x) stem = stem := List.map_id stem
  simpa only [fields,List.map_append,List.map_map,List.map_reverse,List.map_ofFn,
    Function.comp_def,identity,Store.file] using graph

private theorem frameCode_definable₂ (stem : List M) (path : List Bool) :
    𝚺ᴬ₁-Function₂ (fun gap code => (frameFromCode stem path gap code).code) := by
  let buffer := fun code => registers (stem ++ (Store.ofCode code).file) 0
  letI : 𝚺ᴬ₁-Function₁ buffer := frameRegister_definable₁ stem
  have takeStore : 𝚺ᴬ₁.DefinableFunction (fun v : Fin 2 → M => v 1) := by definability
  have load : 𝚺ᴬ₁.DefinableFunction (fun v : Fin 2 → M => buffer (v 1)) :=
    Bounding.HierarchySymbol.DefinableFunction₁.comp (F := buffer) takeStore
  let padded := fun v : Fin 2 → M => repeatBit false (v 0) (buffer (v 1))
  have blanked : 𝚺ᴬ₁.DefinableFunction padded :=
    Bounding.HierarchySymbol.DefinableFunction₂.comp (F := repeatBit false) (by definability) load
  let bits := packWord (M := M) (trimPC path)
  letI : 𝚺ᴬ₁-Function₁ bits := packWord_definable₁ (trimPC path)
  have word : 𝚺ᴬ₁.DefinableFunction (fun v => bits (padded v)) :=
    Bounding.HierarchySymbol.DefinableFunction₁.comp (F := bits) blanked
  letI : 𝚺ᴬ₁-Function₃ (encode (M := M)) := encode_definable
  have state : 𝚺ᴬ₁.DefinableFunction (fun _ : Fin 2 → M => (Engine.Port.root : M)) := by definability
  have head : 𝚺ᴬ₁.DefinableFunction (fun _ : Fin 2 → M => (1 : M)) := by definability
  exact Bounding.HierarchySymbol.DefinableFunction₃.comp (F := encode) state head word

/-- Reachability at a fixed instruction boundary. The arithmetic-model
witness retains the unused loader registers and all padding cells. -/
def ReachedAt (origin : M) (stem : List M) (path : List Bool) (code : M) : Prop :=
  len code = 12 ∧ Engine.Clean (trimPC path) ∧
  ∃ gap : M, (74 : M) ≤ ((trimPC path).length : M)+gap ∧
    Reaches referenceMachine origin (frameFromCode stem path gap code).code

theorem reachedAt_definable (origin : M) (stem : List M) (path : List Bool) :
    𝚺ᴬ₁-Predicate (ReachedAt origin stem path) := by
  have code := frameCode_definable₂ stem path
  change 𝚺ᴬ₁.Definable (fun v : Fin 1 → M => ReachedAt origin stem path (v 0))
  classical
  by_cases clean : Engine.Clean (trimPC path)
  · simp only [ReachedAt,clean,true_and]
    definability
  · simp only [ReachedAt,clean,false_and,and_false]
    definability

theorem reachedAt_of_frame {origin : M} (frameState : Frame M) (ready : frameState.Prepared)
    (reached : Reaches referenceMachine origin frameState.code) :
    ReachedAt origin (frameState.values.take (frameState.values.length-12)) frameState.path
      (storeOf frameState.values).code := by
  obtain ⟨gap,normalized,span⟩ := frame_trim frameState
  refine ⟨Store.len_code _,trimPC_clean ready.1,gap,span ▸ ready.2.2,?_⟩
  have file := file_storeOf frameState.values (le_trans (by decide : 12 ≤ 13) ready.2.1)
  rw [frameFromCode,Frame.code,Store.ofCode_code,file,List.take_append_drop,← normalized]
  exact reached

theorem frameFromCode_prepared (stem : List M) (nonempty : 0 < stem.length)
    (path : List Bool) (gap code : M) (clean : Engine.Clean (trimPC path))
    (margin : (74 : M) ≤ ((trimPC path).length : M)+gap) :
    (frameFromCode stem path gap code).Prepared := by
  refine ⟨clean,?_,margin⟩
  simp only [frameFromCode,List.length_append,Store.length_file]
  omega

theorem advance_reachedAt {origin s t : M} {stem : List M} (nonempty : 0 < stem.length)
    {p q : List Bool} (reached : ReachedAt origin stem p s)
    (transition : step referenceProgram (atPath p (Store.ofCode s)) =
      some (atPath q (Store.ofCode t))) (wellFormed : len t = (12 : M)) :
    ReachedAt origin stem q t := by
  obtain ⟨_,clean,gap,margin,reached⟩ := reached
  let input := frameFromCode stem p gap s
  have prepare : input.Prepared := frameFromCode_prepared stem nonempty p gap s clean margin
  have projects := frameFromCode_project stem p gap s
  have move : step referenceProgram (projectFrame input) = some (atPath q (Store.ofCode t)) := by
    simpa only [input,projects] using transition
  obtain ⟨output,executed,moved,ready,projection⟩ := advance_frame prepare move
  obtain ⟨size,preserved⟩ := frame_file_unchanged executed
  have inputSize : input.values.length = stem.length+12 := by
    simp only [input,frameFromCode,List.length_append,Store.length_file]
  have splitAt : input.values.length-12 = stem.length := by omega
  have retained : output.values.take (output.values.length-12) = stem := by
    rw [splitAt] at preserved
    rw [size,splitAt,preserved]
    change (stem ++ (Store.ofCode s).file).take stem.length = stem
    simp
  have read : storeOf output.values = Store.ofCode t := congrArg PathState.registers projection
  have branch : trimPC output.path = trimPC q := congrArg PathState.pc projection
  have count : 12 ≤ output.values.length := by rw [size,inputSize]; omega
  have file : output.values = stem ++ (Store.ofCode t).file := by
    rw [← read,file_storeOf output.values count,← retained,List.take_append_drop]
  obtain ⟨newGap,normalized,span⟩ := frame_trim output
  rw [branch,file] at normalized
  refine ⟨wellFormed,branch ▸ trimPC_clean ready.1,newGap,?_,(reached.trans moved).trans ?_⟩
  · have enough := ready.2.2
    rwa [span,branch] at enough
  · rw [normalized]
    exact Reaches.refl _ _

theorem halt_reachedAt {origin s : M} {stem : List M} (nonempty : 0 < stem.length)
    {p : List Bool} (reached : ReachedAt origin stem p s)
    (terminal : step referenceProgram (atPath p (Store.ofCode s)) = none) :
    ReachesHalt origin := by
  obtain ⟨_,clean,gap,margin,reached⟩ := reached
  let input := frameFromCode stem p gap s
  have prepare : input.Prepared := frameFromCode_prepared stem nonempty p gap s clean margin
  have projects := frameFromCode_project stem p gap s
  rw [← projects] at terminal
  obtain ⟨l,r,stop⟩ := halt_frame prepare terminal
  exact ⟨l,r,reached.trans stop⟩

end PalomarI3380.Compiler
