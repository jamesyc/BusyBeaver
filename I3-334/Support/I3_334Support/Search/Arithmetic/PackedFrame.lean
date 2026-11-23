module
public import I3_334Support.Search.Arithmetic.FrameNormalForm
public import I3_334Support.Engine.Arithmetic.RegisterWords
@[expose] public section

namespace PalomarI3380.Compiler

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticMachine
open ArithmeticMachine.Reference (registers cell)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem trimPC_idem (path : List Bool) : trimPC (trimPC path) = trimPC path :=
  List.rdropWhile_idempotent (!·) path

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

theorem packedFrame_definable₂ (root : Nat) (stem : List M) (path : List Bool) :
    𝚺ᴬ₁-Function₂ (fun gap code => cell root 1
      (packWord (trimPC path) (repeatBit false gap (registers (stem ++ (Store.ofCode code).file) 0)))) := by
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
  have state : 𝚺ᴬ₁.DefinableFunction (fun _ : Fin 2 → M => (root : M)) := by definability
  have head : 𝚺ᴬ₁.DefinableFunction (fun _ : Fin 2 → M => (1 : M)) := by definability
  exact Bounding.HierarchySymbol.DefinableFunction₃.comp (F := encode) state head word

end PalomarI3380.Compiler
