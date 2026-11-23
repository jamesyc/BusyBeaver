module
public import I3_334.Tape.LiteralRegister
public import I3_334.Simulation.FrameExecution
@[expose] public section

namespace PalomarI3334.Stock

open PalomarI3380 PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell registers)
open PalomarI3334.LiteralDecoder
open Decoder (Result)
open Engine (breakPath breakPadding registerValue zeroDecrement zeros)
open Control (root cut continuePort)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def LiteralRealizes (s : Frame M) : Outcome M → Prop
  | .invalid => False
  | .halt => ∃ l r : M, Reaches machine s.code (cell 334 l r)
  | .next t => Progress machine s.code t.code ∧ Decoder.Clean t.path ∧
      t.values.length = s.values.length ∧ s.span ≤ t.span

private theorem ordinaryDonor {q : Nat} {b : Bool} (normal : special q b = false) :
    donor q b = false := by
  cases b <;> simp [donor, special] at normal ⊢
  exact ⟨normal.1.2, normal.2⟩

private theorem image_continue (skip : Fin 5) : image (continuePort skip.val) = continuePort skip.val := by
  revert skip
  decide +kernel

private theorem image_break (skip : Bool) : image (Control.breakPort skip) = Control.breakPort skip := by
  cases skip <;> decide +kernel

private theorem normal_arm {input : List Bool} {d : Result}
    (facts : Decoder.Decodes root [] input d) (h : d.command ≠ .continue ⟨1,by decide⟩) :
    special d.node d.read = false := by
  cases branch : special d.node d.read
  · rfl
  · exact (h (special_command facts branch)).elim

/-- The donor's matched window has already skipped the first one and
moved left past the next surviving one. Those surviving bits agree with
the continued instruction pointer and supply exactly the same gap. -/
private theorem donor_continue {d : Result} {initial gap : M} (rs : List M)
    (h : Replayed d initial (repeatBit false gap (registers rs 0)))
    (usesDonor : donor d.node d.read = true)
    (bounded : Control.boundedZeros 0 d.before = true) :
    Progress machine initial (frame (cut d.before 1).reverse
      ((gap+1)+1+((d.before.length-(cut d.before 1).length : Nat) : M)) rs) := by
  let w := leftCode d.before % 8
  let p := d.before.drop (donorWidth w)
  let suffix := repeatBit false gap (registers rs 0)
  have shape : d.before = donorPrefix w ++ p := h.donorShape usesDonor
  have proof := h.reaches
  have first : Progress machine initial (fromLeft 9 (packWord p 1) (packWord (donorRight w) suffix)) := by
    simpa only [literalExit, usesDonor, ↓reduceIte, p, w, suffix] using proof
  by_cases short : w % 4 = 3
  · have branch : d.before = true :: true :: p := by
      simpa only [donorPrefix, short, ↓reduceIte, List.cons_append, List.nil_append] using shape
    have valid : Control.boundedZeros 0 p = true := by
      simpa only [branch, Control.boundedZeros] using bounded
    have run := Control.dispatchFrom Control.literalRows p 0 (by decide) valid (packWord (donorRight w) suffix)
    have result := first.trans run
    have size : (true :: true :: p).length - (true :: p).length = 1 := by
      simp only [List.length_cons]
      omega
    have word : packWord (donorRight w) suffix =
        pushBit true (repeatBit false ((gap+1)+1+1) (registers rs 0)) := by
      simp only [donorRight, donorWidth, short, ↓reduceIte, List.replicate_succ, List.replicate_zero, packWord_cons,
        packWord_nil, repeatBit_succ, suffix]
    rw [word] at result
    simp only [branch, cut, Decoder.cut_zero, size, List.reverse_cons, frame, packWord_append,
      packWord_cons, packWord_nil, Nat.cast_one]
    exact result
  · have branch : d.before = true :: false :: true :: p := by
      simpa only [donorPrefix, short, ↓reduceIte, List.cons_append, List.nil_append] using shape
    have valid : Control.boundedZeros 0 p = true :=
      Control.boundedZeros_tail (Control.boundedZeros_tail (Control.boundedZeros_tail (branch ▸ bounded)))
    have run := Control.dispatchFrom Control.literalRows p 0 (by decide) valid (packWord (donorRight w) suffix)
    have result := first.trans run
    have size : (true :: false :: true :: p).length - (false :: true :: p).length = 1 := by
      simp only [List.length_cons]
      omega
    have word : packWord (donorRight w) suffix =
        pushBit true (pushBit false (repeatBit false ((gap+1)+1+1) (registers rs 0))) := by
      simp only [donorRight, donorWidth, short, ↓reduceIte, List.replicate_succ, List.replicate_zero, packWord_cons,
        packWord_nil, repeatBit_succ, suffix]
    rw [word] at result
    simp only [branch, cut, Decoder.cut_zero, size, List.reverse_cons, frame, packWord_append,
      packWord_cons, packWord_nil, Nat.cast_one]
    exact result

private theorem literal_continue {input : List Bool} {d : Result}
    (found : Decoder.follow 70 root [] input = some d)
    (facts : Decoder.Decodes root [] input d) {skip : Fin 5} (command : d.command = .continue skip)
    (gap : M) (rs : List M) (positive : 0 < gap) :
    Progress machine (frame d.path gap rs)
      (frame (cut d.before skip.val).reverse
        (gap+1+((d.before.length-(cut d.before skip.val).length : Nat) : M)) rs) := by
  have shape := facts.leaf
  have target := facts.target
  rw [command] at shape target
  obtain ⟨direction, write, _, enough, bounded⟩ := shape
  change (Decoder.transition d.node d.read).target = continuePort skip.val at target
  have finish := Control.continueRun Control.literalRows d.before skip.val (by have h := skip.isLt; omega)
    bounded enough (repeatBit false (gap+1) (registers rs 0))
  by_cases exceptional : special d.node d.read = true
  · have equal := (special_command facts exceptional).symm.trans command
    injection equal with eq
    subst skip
    rcases zero_or_succ gap with zero | ⟨rest, rfl⟩
    · exact (ne_of_gt positive zero).elim
    · let tail := repeatBit false rest (registers rs 0)
      have walk := root_replay found tail
      have start : frame d.path (rest+1) rs =
          cell root 1 (packWord d.path (gapWord d tail)) := by
        simp only [frame, gapWord, exceptional, ↓reduceIte, repeatBit_succ, tail]
      rw [start]
      cases usesDonor : donor d.node d.read
      · have step := walk.reaches
        simp only [literalExit, usesDonor, Bool.false_eq_true, direction, ↓reduceIte,
          target, show image (continuePort 1) = continuePort 1 from by decide +kernel,
          write, gapWord, exceptional, tail, ← repeatBit_succ] at step
        simpa only [gapWord, exceptional, ↓reduceIte, tail, repeatBit_succ] using
          step.trans (by simpa only [frame, ← repeatBit_add] using finish)
      · exact donor_continue rs walk usesDonor bounded
  · have normal : special d.node d.read = false := Bool.of_not_eq_true exceptional
    have noDonor := ordinaryDonor normal
    let tail := repeatBit false gap (registers rs 0)
    have step := (root_replay found tail).reaches
    simp only [literalExit, gapWord, normal, noDonor, direction, write, target, image_continue,
      Bool.false_eq_true, ↓reduceIte, tail, ← repeatBit_succ] at step
    exact step.trans (by simpa only [frame, ← repeatBit_add] using finish)

theorem executeWith_literal (s : Frame M) (clean : Decoder.Clean s.path)
    (length : 13 ≤ s.values.length) {pad : Nat} (room : (pad : M) ≤ s.gap) {d : Result}
    (found : Decoder.follow 70 root [] (s.path ++ zeros pad) = some d)
    (margin : armMargin d ≤ d.rest.length) :
    LiteralRealizes s (executeWith s pad) := by
  have live : 0 < Decoder.height root := by rw [Decoder.root_shape.1]; decide
  obtain ⟨facts⟩ := Decoder.follow_facts 70 ⟨root,by decide⟩ [] _ live Decoder.root_shape.2 found
  let gap := (d.rest.length : M) + (s.gap - (pad : M))
  obtain ⟨start, _⟩ := splitFrame s clean room facts
  change s.code = frame d.path gap s.values at start
  have preserved := executeWith_realizes s clean length room found margin
  have eq : executeWith s pad = advanceFrame s.values d gap := by
    simp only [executeWith, found, margin, ↓reduceIte, gap]
  rw [eq] at preserved ⊢
  cases command : d.command with
  | halt =>
    let tail := repeatBit false gap (registers s.values 0)
    let edge := Decoder.transition d.node d.read
    have normal := normal_arm facts (by rw [command]; decide)
    have shape := facts.leaf
    have target := facts.target
    rw [command] at shape target
    change edge.right = true at shape
    change edge.target = 344 at target
    have port : image 344 = 334 := by decide +kernel
    have run := (root_replay found tail).reaches
    simp only [advanceFrame, command, LiteralRealizes]
    refine ⟨pushBit edge.write (packWord d.before 1),tail, ?_⟩
    simpa only [start, frame, literalExit, gapWord, normal, ordinaryDonor normal, Bool.false_eq_true,
      ↓reduceIte, edge, shape, target, port, tail] using run.reach
  | «break» skip =>
    let tail := repeatBit false gap (registers s.values 0)
    have normal := normal_arm facts (by rw [command]; intro clash; cases clash)
    have shape := facts.leaf
    have target := facts.target
    rw [command] at shape target
    obtain ⟨direction,write,_,_,bounded⟩ := shape
    change (Decoder.transition d.node d.read).target = Control.breakPort skip at target
    have step := (root_replay found tail).reaches
    simp only [literalExit, gapWord, ordinaryDonor normal, normal, direction, write, target,
      image_break, Bool.false_eq_true, ↓reduceIte, tail, ← repeatBit_succ] at step
    have back := Control.breakRun Control.literalRows skip d.before bounded
      (repeatBit false (gap+1) (registers s.values 0))
    simp only [advanceFrame, command, LiteralRealizes, Realizes] at preserved ⊢
    refine ⟨?_,preserved.2⟩
    rw [start]
    exact step.trans (by simpa only [Frame.code, frame, ← repeatBit_add] using back)
  | «continue» skip =>
    have extra : 0 < d.rest.length := by simpa only [armMargin, command, Nat.one_le_iff_ne_zero,
      Nat.pos_iff_ne_zero] using margin
    have positive : 0 < gap := lt_of_lt_of_le (by exact_mod_cast extra)
      (le_add_of_nonneg_right (Arithmetic.zero_le _))
    have step := literal_continue found facts command gap s.values positive
    simp only [advanceFrame, command, LiteralRealizes, Realizes] at preserved ⊢
    exact ⟨by rw [start]; exact step,preserved.2⟩
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
    have cycle := literalRegisterCycle (register_route found facts command) remain a value before after index
    simp only [advanceFrame, command, LiteralRealizes, Realizes, read, update] at preserved ⊢
    refine ⟨?_,preserved.2⟩
    rw [start,values,gapEq]
    simpa only [Frame.code, add_assoc,add_left_comm,add_comm] using cycle

theorem execute_literal (s : Frame M) (ready : s.Prepared) : LiteralRealizes s (execute s) := by
  let pad := frameCapacity - s.path.length
  let input := s.path ++ zeros pad
  have length : 84 ≤ input.length := by
    simp only [input,pad,frameCapacity,List.length_append,List.length_replicate]
    omega
  obtain ⟨d,found,⟨facts⟩⟩ := Decoder.decode input (by omega)
  have suffix := facts.bounded
  rw [Decoder.root_shape.1] at suffix
  have room : armMargin d ≤ d.rest.length := by
    cases command : d.command <;> simp only [armMargin,command]
    case register dec rank => have h := rank.isLt; omega
    case «continue» skip => omega
    all_goals exact Nat.zero_le _
  exact executeWith_literal s ready.1 ready.2.1 (prefixRoom s ready) found room

end PalomarI3334.Stock
