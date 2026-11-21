module
public import I3_380.Engine.Arithmetic.FrameRegister
public import I3_380.Engine.Paths
public import I3_380.Engine.Interpreter
public import I3_380.Engine.LogicalStep
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.Reference

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Engine (Decoded DecodedFrom breakPath breakPadding stripThrough registerValue zeroDecrement)
open Engine.Port

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

structure Frame (M : Type) where
  path : List Bool
  gap : M
  values : List M

noncomputable def Frame.code (s : Frame M) : M := frame s.path s.gap s.values

def Frame.Prepared (s : Frame M) : Prop :=
  Engine.Clean s.path ∧ 13 ≤ s.values.length ∧ (74 : M) ≤ (s.path.length : M)+s.gap

inductive Outcome (M : Type) where
  | invalid
  | next (state : Frame M)
  | halt

noncomputable def executeDecoded (rs : List M) (d : Decoded) (gap : M) : Outcome M :=
  match d.command with
  | .halt => .halt
  | .break skip =>
    .next ⟨(breakPath skip d.before).reverse,gap+1+(breakPadding skip d.before : M),rs⟩
  | .continue false => .next ⟨d.before.reverse,gap+1,rs⟩
  | .continue true =>
    let path := stripThrough true d.before
    .next ⟨path.reverse,gap+1+((d.before.length-path.length : Nat) : M),rs⟩
  | .register dec r =>
    let i := rs.length - (r.val+1)
    let value := rs[i]?.getD 0
    let skip := zeroDecrement dec value
    .next ⟨(breakPath skip d.path.reverse).reverse,
      gap+(Engine.bit dec : M)+(breakPadding skip d.path.reverse : M),rs.set i (registerValue dec value)⟩

/-- Restrict the static lookahead to an ordinary finite control word.
Every omitted cell is a padding zero and is kept in the model-valued gap. -/
noncomputable def execute (s : Frame M) : Outcome M :=
  let pad := 74 - s.path.length
  match Engine.follow 59 root [] (s.path ++ Engine.zeros pad) with
  | some d => executeDecoded s.values d ((d.rest.length : M) + (s.gap - (pad : M)))
  | none => .invalid

private theorem frontGap (s : Frame M) (ready : s.Prepared) : ((74-s.path.length : Nat) : M) ≤ s.gap := by
  by_cases long : 74 ≤ s.path.length
  · simp [Nat.sub_eq_zero_of_le long]
  · have sum : ((74-s.path.length : Nat) : M)+(s.path.length : M) = 74 := by
      exact_mod_cast Nat.sub_add_cancel (Nat.le_of_not_ge long)
    have available := ready.2.2
    rw [← sum,add_comm (s.path.length : M) s.gap] at available
    exact le_of_add_le_add_right available

private theorem splitFrame (s : Frame M) (ready : s.Prepared) {d : Decoded}
    (found : Engine.follow 59 root [] (s.path ++ Engine.zeros (74-s.path.length)) = some d) :
    let gap := (d.rest.length : M)+(s.gap-((74-s.path.length : Nat) : M))
    s.code = frame d.path gap s.values ∧
      (s.path.length : M)+s.gap = (d.path.length : M)+gap := by
  let pad := 74-s.path.length
  let rest := s.gap-(pad : M)
  have sGap : (pad : M)+rest = s.gap := by
    rw [add_comm,tsub_add_cancel_of_le (frontGap s ready)]
  have dFacts := Engine.decode_facts _ found
  have zeros := dFacts.rest_zeros ready.1
  have words : d.path ++ Engine.zeros d.rest.length = s.path ++ Engine.zeros pad :=
    (congrArg (d.path ++ ·) zeros.symm).trans dFacts.consumed
  dsimp only [Frame.code]
  constructor
  · change frame s.path s.gap s.values = frame d.path ((d.rest.length : M)+rest) s.values
    unfold frame
    conv_lhs => rw [← sGap,add_comm (pad : M) rest,repeatBit_add]
    rw [repeatBit_cast,← packWord_append,← words,packWord_append,← repeatBit_cast]
    rw [add_comm (d.rest.length : M) rest,repeatBit_add]
  · change (s.path.length : M)+s.gap = (d.path.length : M)+((d.rest.length : M)+rest)
    have len := congrArg List.length words
    simp only [List.length_append,List.length_replicate] at len
    conv_lhs => rw [← sGap,← add_assoc,← Nat.cast_add,← len,Nat.cast_add,add_assoc]

private theorem prefix_present (path : List Bool) : 74 ≤ (path ++ Engine.zeros (74-path.length)).length := by
  simp only [List.length_append,List.length_replicate]
  omega

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- The arithmetic interpreter never needs more than the first 59 bits
of a prepared frame. The arithmetic gap left after decoding contains
at least the thirteen selector cells and two flank zeros. -/
theorem decodePrepared (s : Frame M) :
    ∃ d,
      Engine.follow 59 root [] (s.path ++ Engine.zeros (74-s.path.length)) = some d ∧
      15 ≤ d.rest.length := by
  let input := s.path ++ Engine.zeros (74-s.path.length)
  have len : 74 ≤ input.length := prefix_present s.path
  obtain ⟨d,found⟩ := Engine.decode_root input (by omega)
  have bound := (Engine.decode_facts _ found).lengthBound
  rw [Engine.rootHeight] at bound
  exact ⟨d,found,by omega⟩

def ReachesHalt (source : M) : Prop :=
  ∃ l r : M, Reaches referenceMachine source (cell 394 l r)

def Realizes (s : Frame M) : Outcome M → Prop
  | .invalid => False
  | .halt => ReachesHalt s.code
  | .next t => Reaches referenceMachine s.code t.code ∧ t.Prepared


/-- Realize each decoded branch by the packed machine clock and maintain
the preparation conditions required by the next branch. -/
theorem execute_realizes (s : Frame M) (ready : s.Prepared) :
    Realizes s (execute s) := by
  obtain ⟨d,found,margin⟩ := decodePrepared s
  let gap := (d.rest.length : M)+(s.gap-((74-s.path.length : Nat) : M))
  obtain ⟨configuration,span⟩ := splitFrame s ready found
  change s.code = frame d.path gap s.values at configuration
  change (s.path.length : M)+s.gap = (d.path.length : M)+gap at span
  have enough : (74 : M) ≤ (d.path.length : M)+gap := span ▸ ready.2.2
  let tail := repeatBit false gap (registers s.values 0)
  have walk := Engine.decode_facts _ found
  have run := follow_reaches walk (by decide) (by rw [Engine.rootHeight]; decide) Engine.root_valid 1 tail
  change Reaches referenceMachine (frame d.path gap s.values) (destination d 1 tail) at run
  have shape := walk.shape
  have port := walk.port
  have spanLeaf : (d.path.length : M)+gap = (d.before.length : M)+1+gap := by
    simp only [Decoded.path,List.length_append,List.length_reverse,List.length_singleton,Nat.cast_succ]
  have canReturn (q : Nat) (target : d.transition.target = q)
      (direction : d.transition.right = false) (write : d.transition.write = false) :
      Reaches referenceMachine s.code (fromLeft q (packWord d.before 1)
        (repeatBit false (gap+1) (registers s.values 0))) := by
    rw [configuration]
    simpa only [destination,target,direction,write,Bool.false_eq_true,↓reduceIte,repeatBit_succ,tail] using run
  unfold execute
  dsimp only
  rw [found]
  change Realizes s (executeDecoded s.values d gap)
  cases command : d.command with
  | halt =>
    rw [command] at shape port
    change d.transition.right = true at shape
    change 394 = d.transition.target at port
    simp only [executeDecoded,command,Realizes,ReachesHalt]
    exact ⟨pushBit d.transition.write (packWord d.before 1),tail,by
      simpa only [configuration,destination,shape,↓reduceIte,← port] using run⟩
  | «break» skip =>
    rw [command] at shape port
    obtain ⟨direction,write,valid⟩ := shape
    have advance := canReturn (breakPort skip) port.symm direction write
    have back := breakRun skip d.before valid (repeatBit false (gap+1) (registers s.values 0))
    simp only [executeDecoded,command,Realizes,Frame.code,Frame.Prepared]
    refine ⟨advance.trans ?_,Engine.clean_break d.before skip walk.before_valid,ready.2.1,?_⟩
    · simpa only [frame,← repeatBit_add] using back
    · have length : (d.before.length : M) ≤ ((breakPath skip d.before).length : M) +
          (breakPadding skip d.before : M) := by exact_mod_cast Engine.break_length skip d.before
      have extended := add_le_add_left length (gap+1)
      rw [spanLeaf] at enough
      rw [List.length_reverse]
      apply enough.trans
      convert extended using 1 <;> ac_rfl
  | «continue» skip =>
    rw [command] at shape port
    obtain ⟨direction,write,valid,hasOne⟩ := shape
    cases skip with
    | false =>
      have advance := canReturn (dispatch 0) port.symm direction write
      have back := dispatchFrom d.before 0 (by decide) valid (repeatBit false (gap+1) (registers s.values 0))
      simp only [executeDecoded,command,Realizes,Frame.code,Frame.Prepared]
      refine ⟨advance.trans back,⟨d.before.reverse,0,by simp,walk.before_valid⟩,ready.2.1,?_⟩
      rw [spanLeaf] at enough
      rw [List.length_reverse]
      simpa only [add_assoc,add_comm (1 : M) gap] using enough
    | true =>
      let p := stripThrough true d.before
      let padding := d.before.length-p.length
      have advance := canReturn Engine.Port.continueOne port.symm direction write
      have back := continueOne d.before valid (hasOne rfl) (repeatBit false (gap+1) (registers s.values 0))
      simp only [executeDecoded,command,Realizes,Frame.code,Frame.Prepared]
      refine ⟨advance.trans ?_,Engine.clean_continue d.before walk.before_valid,ready.2.1,?_⟩
      · simpa only [frame,← repeatBit_add] using back
      · have length : p.length+padding = d.before.length :=
          Nat.add_sub_of_le (Engine.stripThrough_length ..)
        have castLength : (p.length : M)+(padding : M) = (d.before.length : M) := by exact_mod_cast length
        rw [spanLeaf] at enough
        rw [List.length_reverse]
        change (74 : M) ≤ (p.length : M)+(gap+1+(padding : M))
        convert enough using 1
        rw [← castLength]
        ac_rfl
  | register dec r =>
    obtain ⟨a,before,value,after,values,index,read,update⟩ := Engine.split_register s.values r ready.2.1
    let count := r.val+1
    let flank := r.val+3
    have need : flank ≤ d.rest.length := by have bounded := r.isLt; dsimp [flank]; omega
    let remain := ((d.rest.length-flank : Nat) : M)+(s.gap-((74-s.path.length : Nat) : M))
    have gapEq : gap = remain+2+(count : M) := by
      have parts : (d.rest.length-flank)+2+count = d.rest.length := by dsimp [flank,count]; omega
      have castParts : ((d.rest.length-flank : Nat) : M)+2+(count : M) = (d.rest.length : M) := by
        exact_mod_cast parts
      dsimp [gap,remain]
      rw [← castParts]
      ac_rfl
    have cycle := registerCycle (register_route walk command) remain a value before after index
    simp only [executeDecoded,command,Realizes,Frame.code,Frame.Prepared,read,update]
    change frame s.path s.gap s.values = frame d.path gap s.values at configuration
    rw [configuration,values,gapEq]
    refine ⟨?_,Engine.clean_break d.path.reverse _ (by simpa using walk.validPrefix),?_,?_⟩
    · simpa only [add_assoc,add_left_comm,add_comm] using cycle
    · simpa only [List.length_append,List.length_cons,values] using ready.2.1
    · let skip := zeroDecrement dec value
      have shorter : (d.path.length : M) ≤ ((breakPath skip d.path.reverse).length : M) +
          (breakPadding skip d.path.reverse : M) := by
        exact_mod_cast (by simpa using Engine.break_length skip d.path.reverse)
      have extended : (d.path.length : M)+gap ≤
          gap + ((breakPath skip d.path.reverse).length : M) +
            (breakPadding skip d.path.reverse : M) := by
        simpa only [add_assoc,add_left_comm,add_comm] using add_le_add_left shorter gap
      rw [List.length_reverse,← gapEq]
      calc
        74 ≤ _ := enough.trans extended
        _ ≤ _ + (Engine.bit dec : M) := le_add_of_nonneg_right (Arithmetic.zero_le _)
        _ = _ := by ac_rfl

def Frame.logical (s : Frame M) : Engine.LogicalState M := ⟨s.path,s.values⟩

def Outcome.logical : Outcome M → Option (Engine.LogicalState M)
  | .next s => some s.logical
  | .halt | .invalid => none

private theorem decoded_projection (rs : List M) (d : Decoded) (gap : M) :
    (executeDecoded rs d gap).logical = Engine.logicalDecoded rs d := by
  cases command : d.command with
  | halt | «break» | register => simp [executeDecoded,command,Outcome.logical,Engine.logicalDecoded,Frame.logical]
  | «continue» skip => cases skip <;> simp [executeDecoded,command,Outcome.logical,Engine.logicalDecoded,Frame.logical]

/-- Use the same control and register semantics for standard traces
and for frame executions in a model. Padding is handled by each tape adapter. -/
theorem logical_projection (s : Frame M) :
    (execute s).logical = Engine.logicalNext s.logical := by
  obtain ⟨d,short,_⟩ := decodePrepared s
  obtain ⟨e,long⟩ := Engine.decode_root (s.path ++ Engine.zeros 59) (by simp)
  simp only [execute,short,Engine.logicalNext,Frame.logical,long,Option.bind_some]
  rw [decoded_projection]
  exact Engine.logical_same_arm s.path s.values _ _ short long

end PalomarI3380.ArithmeticMachine.Reference
