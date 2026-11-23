module
public import I3_334.Simulation.Bootstrap
public import I3_334.Simulation.ReferenceTree
public import I3_334Support.Search.Compiler.RegisterFile
@[expose] public section

namespace PalomarI3334

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.ArithmeticMachine
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Control (root cut)
open Decoder (Result follow transition height exitAt)
open Stock (Frame Outcome execute advanceFrame armMargin frameCapacity)


theorem cut_eq (path : List Bool) (count : Nat) : cut path count = stripMany true count path := by
  induction path generalizing count with
  | nil =>
    induction count with
    | zero => rfl
    | succ n ih => exact ih
  | cons b path ih =>
    cases count with
    | zero => exact Decoder.cut_zero _
    | succ n =>
      cases b
      · rw [stripMany_miss (by decide : false ≠ true)]
        exact ih (n+1)
      · rw [stripMany_hit]
        exact ih n

def project {V : Type} [OfNat V 0] (s : Frame V) : PathState V := atPath s.path (storeOf s.values)

def nextFrame {V : Type} [NatCast V] [OfNat V 0] [OfNat V 1] [Add V] [Sub V] [DecidableEq V]
    (s : Frame V) : Option (Frame V) :=
  match execute s with
  | .next t => some t
  | _ => none

def nextFrameWith {V : Type} [NatCast V] [OfNat V 0] [OfNat V 1] [Add V] [Sub V]
    [DecidableEq V] (s : Frame V) (pad : Nat) : Option (Frame V) :=
  match Stock.executeWith s pad with
  | .next t => some t
  | _ => none

theorem project_with {V : Type} [NatCast V] [OfNat V 0] [OfNat V 1] [Add V] [Sub V]
    [DecidableEq V] (s : Frame V) (length : 12 ≤ s.values.length) {pad : Nat} {d : Result}
    (found : follow 70 root [] (s.path ++ Engine.zeros pad) = some d)
    (margin : armMargin d ≤ d.rest.length) :
    (nextFrameWith s pad).map project = Compiler.step referenceProgram (project s) := by
  have active : 0 < height root := by rw [Decoder.root_shape.1]; decide
  obtain ⟨facts⟩ := Decoder.follow_facts 70 ⟨root, by decide⟩ [] _ active Decoder.root_shape.2 found
  have walkInfo := tableNode_walk found
  have inPath : walk referenceProgram s.path = (d.command.op, d.path) := by
    have result : walk referenceProgram (s.path ++ Engine.zeros pad) = (d.command.op, d.path) :=
      Prod.ext walkInfo.1 walkInfo.2
    simpa only [walk_zeros] using result
  have executing : Stock.executeWith s pad = advanceFrame s.values d ((d.rest.length : V) + (s.gap - (pad : V))) := by
    simp only [Stock.executeWith, found, margin, ↓reduceIte]
  simp only [nextFrameWith, executing, Compiler.step, project, atPath, walk_trim, inPath]
  have leaf := facts.leaf
  cases command : d.command with
  | halt => simp [advanceFrame, command, Decoder.Exit.op, Op.effect]
  | «break» skip =>
    rw [command] at leaf
    obtain ⟨_, _, rfl, readOne, _⟩ := leaf
    simp [advanceFrame, command, Decoder.Exit.op, Op.effect, project, destination, atPath,
      Engine.breakPath, Result.path, List.reverse_append, readOne, stripMany, Engine.stripThrough]
  | «continue» skip =>
    rw [command] at leaf
    have readOne := leaf.2.2.1
    simp [advanceFrame, command, Decoder.Exit.op, Op.effect, project, destination, atPath,
      Result.path, List.reverse_append, readOne, stripMany, Engine.stripThrough, cut_eq]
  | register dec r =>
    let index : Register := ⟨r.val, by have h := r.isLt; omega⟩
    let value := storeOf s.values index
    have update (new : V) := storeOf_set s.values length index new
    cases dec with
    | false =>
      simp [advanceFrame, command, Decoder.Exit.op, Op.effect, project, Engine.registerValue,
        Engine.zeroDecrement, destination, atPath, incrementPath, Engine.breakPath, update, storeOf, index]
    | true =>
      by_cases zero : value = 0
      · have reset : (storeOf s.values).set index 0 = storeOf s.values := by
          rw [← zero]
          exact Store.set_same _ _
        have hZero : s.values[s.values.length - (r.val + 1)]?.getD 0 = 0 := zero
        simp [advanceFrame, command, Decoder.Exit.op, Op.effect, project, Engine.registerValue,
          Engine.zeroDecrement, destination, atPath, Engine.breakPath, update, hZero, reset,
          storeOf, stripMany, index]
      · have hValue : s.values[s.values.length - (r.val + 1)]?.getD 0 ≠ 0 := zero
        simp [advanceFrame, command, Decoder.Exit.op, Op.effect, project, Engine.registerValue,
          Engine.zeroDecrement, destination, atPath, incrementPath, Engine.breakPath, update, hValue,
          storeOf, index]

theorem project_step {V : Type} [NatCast V] [OfNat V 0] [OfNat V 1] [Add V] [Sub V]
    [DecidableEq V] (s : Frame V) (length : 12 ≤ s.values.length) :
    (nextFrame s).map project = Compiler.step referenceProgram (project s) := by
  let pad := frameCapacity - s.path.length
  let input := s.path ++ Engine.zeros pad
  have lengthInput : frameCapacity ≤ input.length := by
    simp only [input, pad, List.length_append, List.length_replicate]
    omega
  obtain ⟨d, found, ⟨facts⟩⟩ := Decoder.decode input (by
    unfold frameCapacity at lengthInput
    omega)
  have suffix := facts.bounded
  rw [Decoder.root_shape.1] at suffix
  have margin : armMargin d ≤ d.rest.length := by
    cases command : d.command <;> simp only [armMargin, command]
    case register dec rank =>
      have h := rank.isLt
      unfold frameCapacity at lengthInput
      omega
    case «continue» skip => unfold frameCapacity at lengthInput; omega
    all_goals exact Nat.zero_le _
  exact project_with s length found margin

end PalomarI3334
