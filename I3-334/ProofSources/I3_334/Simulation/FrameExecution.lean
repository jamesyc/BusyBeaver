module
public import I3_334.Simulation.FramePaths
public import I3_334.Tape.FrameRegister
public import I3_334Support.Engine.RegisterFile
public import I3_334Support.Engine.Arithmetic.StandardTape
@[expose] public section

namespace PalomarI3334.Stock

open PalomarI3380 PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell registers)
open Engine (breakPath breakPadding registerValue zeroDecrement zeros)
open Control (root cut)
open Decoder (Result Clean)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

structure Frame (M : Type) where
  path : List Bool
  gap : M
  values : List M
  deriving DecidableEq

abbrev frameCapacity : Nat := 84

variable {M : Type}

section ModelFrame
variable [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def Frame.code (s : Frame M) : M := frame s.path s.gap s.values

def Frame.span (s : Frame M) : M := (s.path.length : M) + s.gap

def Frame.Prepared (s : Frame M) : Prop :=
  Clean s.path ∧ 13 ≤ s.values.length ∧ (84 : M) ≤ s.span

end ModelFrame

inductive Outcome (M : Type) where
  | invalid
  | next (frame : Frame M)
  | halt
  deriving DecidableEq

def armMargin (d : Result) : Nat :=
  match d.command with
  | .register _ r => r.val + 3
  | .continue _ => 1
  | _ => 0

def advanceFrame [NatCast M] [OfNat M 0] [OfNat M 1] [Add M] [Sub M] [DecidableEq M] (rs : List M) (d : Result) (gap : M) : Outcome M :=
  match d.command with
  | .halt => .halt
  | .break skip =>
    .next ⟨(breakPath skip d.before).reverse, gap + 1 + (breakPadding skip d.before : M), rs⟩
  | .continue skip =>
    let stem := cut d.before skip.val
    .next ⟨stem.reverse, gap + 1 + ((d.before.length - stem.length : Nat) : M), rs⟩
  | .register dec r =>
    let i := rs.length - (r.val + 1)
    let value := rs[i]?.getD 0
    let skip := zeroDecrement dec value
    .next ⟨(breakPath skip d.path.reverse).reverse,
      gap + (Engine.bit dec : M) + (breakPadding skip d.path.reverse : M),
      rs.set i (registerValue dec value)⟩

def executeWith [NatCast M] [OfNat M 0] [OfNat M 1] [Add M] [Sub M] [DecidableEq M] (s : Frame M) (pad : Nat) : Outcome M :=
  match Decoder.follow 70 root [] (s.path ++ zeros pad) with
  | some d =>
    if armMargin d ≤ d.rest.length then advanceFrame s.values d ((d.rest.length : M) + (s.gap - (pad : M)))
    else .invalid
  | none => .invalid

def execute [NatCast M] [OfNat M 0] [OfNat M 1] [Add M] [Sub M] [DecidableEq M] (s : Frame M) : Outcome M :=
  executeWith s (frameCapacity - s.path.length)

variable [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem prefixRoom (s : Frame M) (ready : s.Prepared) :
    ((frameCapacity - s.path.length : Nat) : M) ≤ s.gap := by
  change ((84 - s.path.length : Nat) : M) ≤ s.gap
  by_cases long : 84 ≤ s.path.length
  · simp [Nat.sub_eq_zero_of_le long]
  · have sum : ((84 - s.path.length : Nat) : M) + (s.path.length : M) = 84 := by
      exact_mod_cast Nat.sub_add_cancel (Nat.le_of_not_ge long)
    have available : (84 : M) ≤ (s.path.length : M) + s.gap := ready.2.2
    rw [← sum, add_comm (s.path.length : M) s.gap] at available
    exact le_of_add_le_add_right available

theorem splitFrame (s : Frame M) (clean : Clean s.path) {pad : Nat}
    (room : (pad : M) ≤ s.gap) {d : Result} (walk : Decoder.Decodes root [] (s.path ++ zeros pad) d) :
    let gap := (d.rest.length : M) + (s.gap - (pad : M))
    s.code = frame d.path gap s.values ∧ s.span = (d.path.length : M) + gap := by
  let rest := s.gap - (pad : M)
  have sGap : (pad : M) + rest = s.gap := by rw [add_comm, tsub_add_cancel_of_le room]
  have suffix := walk.rest_zeros clean
  have scanned : walk.scanned = d.path := walk.path
  have words : d.path ++ zeros d.rest.length = s.path ++ zeros pad := by
    rw [← scanned, ← suffix]
    exact walk.consumed
  constructor
  · change frame s.path s.gap s.values = frame d.path ((d.rest.length : M)+rest) s.values
    unfold frame
    conv_lhs => rw [← sGap, add_comm (pad : M) rest, repeatBit_add]
    rw [repeatBit_cast, ← packWord_append, ← words, packWord_append, ← repeatBit_cast]
    rw [add_comm (d.rest.length : M) rest, repeatBit_add]
  · change (s.path.length : M)+s.gap = (d.path.length : M)+((d.rest.length : M)+rest)
    have len := congrArg List.length words
    simp only [List.length_append,List.length_replicate] at len
    conv_lhs => rw [← sGap, ← add_assoc, ← Nat.cast_add, ← len, Nat.cast_add, add_assoc]

def Realizes (s : Frame M) : Outcome M → Prop
  | .invalid => False
  | .halt => ∃ l r : M, Reaches decoderReference s.code (cell 344 l r)
  | .next t => Progress decoderReference s.code t.code ∧ Clean t.path ∧
      t.values.length = s.values.length ∧ s.span ≤ t.span

/-- A root-to-root cycle for each decoder exit. The proof works before
bootstrap as long as the actually chosen arm has enough free space. -/
theorem executeWith_realizes (s : Frame M) (clean : Clean s.path) (length : 13 ≤ s.values.length)
    {pad : Nat} (room : (pad : M) ≤ s.gap) {d : Result}
    (found : Decoder.follow 70 root [] (s.path ++ zeros pad) = some d)
    (margin : armMargin d ≤ d.rest.length) :
    Realizes s (executeWith s pad) := by
  have live : 0 < Decoder.height root := by rw [Decoder.root_shape.1]; decide
  obtain ⟨walk⟩ := Decoder.follow_facts 70 ⟨root, by decide⟩ [] _ live Decoder.root_shape.2 found
  let gap := (d.rest.length : M) + (s.gap - (pad : M))
  obtain ⟨configuration, span⟩ := splitFrame s clean room walk
  change s.code = frame d.path gap s.values at configuration
  change s.span = (d.path.length : M) + gap at span
  let tail := repeatBit false gap (registers s.values 0)
  have scanned : walk.scanned = d.path := walk.path
  have run := walk.run (1 : M) tail
  rw [scanned, packWord_nil] at run
  change Reaches decoderReference (frame d.path gap s.values) (d.destination 1 tail) at run
  have shape := walk.leaf
  have target := walk.target
  let edge := Decoder.transition d.node d.read
  have spanLeaf : s.span = (d.before.length : M) + 1 + gap := by
    rw [span]
    simp only [Result.path, List.length_append, List.length_reverse, List.length_singleton, Nat.cast_succ]
  have canReturn (q : Nat) (atPort : edge.target = q) (different : q ≠ root)
      (dir : edge.right = false) (write : edge.write = false) :
      Progress decoderReference s.code (fromLeft q (packWord d.before 1)
        (repeatBit false (gap+1) (registers s.values 0))) := by
    apply progress_of_ne
    · rw [configuration]
      simpa only [Result.destination, edge, atPort, dir, write, Bool.false_eq_true, ↓reduceIte,
        repeatBit_succ, tail] using run
    · intro same
      have state := congrArg (fun x : M => π₁ x) same
      simp only [Frame.code, frame, cell, fromLeft, encode, Arithmetic.pi₁_pair, nat_cast_inj] at state
      exact different state.symm
  unfold executeWith
  rw [found]
  simp only [margin, ↓reduceIte]
  change Realizes s (advanceFrame s.values d gap)
  cases command : d.command with
  | halt =>
    rw [command] at shape target
    change edge.right = true at shape
    change edge.target = 344 at target
    simp only [advanceFrame, command, Realizes]
    refine ⟨pushBit edge.write (packWord d.before 1), tail, ?_⟩
    simpa only [configuration, Result.destination, edge, shape, target, ↓reduceIte] using run
  | «break» skip =>
    rw [command] at shape target
    obtain ⟨dir, write, _, _, valid⟩ := shape
    have advance := canReturn (Control.breakPort skip) target (Decoder.Exit.port_ne_root (.break skip)) dir write
    have back := Control.breakRun Control.referenceRows skip d.before valid
      (repeatBit false (gap+1) (registers s.values 0))
    simp only [advanceFrame, command, Realizes, Frame.code, Frame.span]
    refine ⟨advance.trans ?_, Decoder.clean_break d.before skip walk.before_valid, trivial, ?_⟩
    · simpa only [frame, ← repeatBit_add] using back
    · have le : (d.before.length : M) ≤ ((breakPath skip d.before).length : M) +
          (breakPadding skip d.before : M) := by exact_mod_cast Engine.break_length skip d.before
      have extended := add_le_add_left le (gap+1)
      simp only [Frame.span] at spanLeaf
      rw [spanLeaf, List.length_reverse]
      simpa only [add_assoc, add_comm, add_left_comm] using extended
  | «continue» skip =>
    rw [command] at shape target
    obtain ⟨dir, write, _, enough, valid⟩ := shape
    let p := cut d.before skip.val
    let padding := d.before.length - p.length
    have advance := canReturn (Control.continuePort skip.val) target (Decoder.Exit.port_ne_root (.continue skip)) dir write
    have back := Control.continueRun Control.referenceRows d.before skip.val (by have h := skip.isLt; omega)
      valid enough (repeatBit false (gap+1) (registers s.values 0))
    simp only [advanceFrame, command, Realizes, Frame.code, Frame.span]
    refine ⟨advance.trans ?_, Decoder.clean_continue d.before skip.val walk.before_valid, trivial, ?_⟩
    · simpa only [frame, ← repeatBit_add] using back
    · have lengths : p.length + padding = d.before.length :=
        Nat.add_sub_of_le (Control.cut_length ..)
      have castLength : (p.length : M) + (padding : M) = (d.before.length : M) := by exact_mod_cast lengths
      simp only [Frame.span] at spanLeaf
      rw [spanLeaf, List.length_reverse]
      change (d.before.length : M) + 1 + gap ≤ (p.length : M) + (gap + 1 + (padding : M))
      rw [← castLength]
      exact le_of_eq (by ac_rfl)
  | register dec r =>
    let r' : Fin 12 := ⟨r.val, by have h := r.isLt; omega⟩
    obtain ⟨a,before,value,after,values,index,read,update⟩ := Engine.split_register s.values r' length
    change after.length = r.val at index
    change s.values[s.values.length-(r.val+1)]?.getD 0 = value at read
    change ∀ value, s.values.set (s.values.length-(r.val+1)) value =
        (a :: before) ++ value :: after at update
    let count := r.val+1
    let flank := r.val+3
    have need : flank ≤ d.rest.length := by simpa only [armMargin, command] using margin
    let remain := ((d.rest.length-flank : Nat) : M)+(s.gap-(pad : M))
    have gapEq : gap = remain+2+(count : M) := by
      have parts : (d.rest.length-flank)+2+count = d.rest.length := by dsimp [flank,count]; omega
      have castParts : ((d.rest.length-flank : Nat) : M)+2+(count : M) = (d.rest.length : M) := by
        exact_mod_cast parts
      dsimp [gap,remain]
      rw [← castParts]
      ac_rfl
    have cycle := registerCycle (decoded_register_route walk command) remain a value before after index
    simp only [advanceFrame, command, Realizes, Frame.code, Frame.span, read, update]
    simp only [Frame.code] at configuration
    rw [configuration, values, gapEq]
    have valid : Decoder.ValidPrefix root d.path := scanned ▸ walk.invariant
    refine ⟨?_, Decoder.clean_break d.path.reverse _ (by simpa using valid), ?_, ?_⟩
    · simpa only [add_assoc,add_left_comm,add_comm] using cycle
    · simp only [List.length_append, List.length_cons]
    · let skip := zeroDecrement dec value
      have shorter : (d.path.length : M) ≤ ((breakPath skip d.path.reverse).length : M) +
          (breakPadding skip d.path.reverse : M) := by
        exact_mod_cast (by simpa using Engine.break_length skip d.path.reverse)
      have extended : (d.path.length : M)+gap ≤
          gap + ((breakPath skip d.path.reverse).length : M) +
            (breakPadding skip d.path.reverse : M) := by
        simpa only [add_assoc,add_left_comm,add_comm] using add_le_add_left shorter gap
      simp only [Frame.span] at span
      rw [span, List.length_reverse, ← gapEq]
      calc
        _ ≤ _ := extended
        _ ≤ _ + (Engine.bit dec : M) := le_add_of_nonneg_right (Arithmetic.zero_le _)
        _ = _ := by
          dsimp only [skip]
          simp only [add_assoc, add_comm, add_left_comm]

theorem prepared_after {s t : Frame M} (ready : s.Prepared) (clean : Clean t.path)
    (length : t.values.length = s.values.length) (span : s.span ≤ t.span) : t.Prepared :=
  ⟨clean, length.symm ▸ ready.2.1, le_trans ready.2.2 span⟩

end PalomarI3334.Stock
