module
public import I3_334.Simulation.LiteralDecoderReplay
public import I3_334.Simulation.FrameSelection
@[expose] public section

namespace PalomarI3334.LiteralDecoder

open PalomarI3380 PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell)
open Decoder (Result transition height follow)
open Stock (Progress RegisterRoute)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

theorem exceptional_target {q : Nat} {bit : Bool} (h : special q bit = true) :
    (transition q bit).target = 8 ∧ height (transition q bit).target = 0 := by
  simp only [special, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, (rfl | rfl) | rfl⟩ := h <;> decide +kernel

theorem special_command {input : List Bool} {d : Result}
    (facts : Decoder.Decodes Control.root [] input d) (h : special d.node d.read = true) :
    d.command = .continue ⟨1,by decide⟩ := by
  have port : d.command.port = 8 := facts.target.symm.trans (exceptional_target h).1
  cases command : d.command with
  | «continue» skip =>
    rw [command] at port
    change 9 - skip.val = 8 at port
    congr 1
    apply Fin.ext
    change skip.val = 1
    have := skip.isLt
    omega
  | register dec rank =>
    have incompatible : ∀ (flag : Bool) (r : Fin 11),
        Decoder.registerPort flag r.val ≠ 8 := by decide +kernel
    rw [command] at port
    exact (incompatible dec rank port).elim
  | «break» skip =>
    rw [command] at port
    cases skip <;> contradiction
  | halt =>
    rw [command] at port
    contradiction

def donor (q : Nat) (b : Bool) : Bool := b && (q == 74 || q == 210)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def gapWord (d : Result) (tail : M) : M :=
  if special d.node d.read then pushBit false tail else tail

/-- An ordinary arm exits at its translated port. The two remaining
donor leaves finish part of the continue before rejoining the dispatcher. -/
noncomputable def literalExit (d : Result) (tail : M) : M :=
  let e := transition d.node d.read
  let left := packWord d.before 1
  if donor d.node d.read then
    let window := leftCode d.before % 8
    fromLeft 9 (packWord (d.before.drop (donorWidth window)) 1) (packWord (donorRight window) tail)
  else if e.right then cell (image e.target) (pushBit e.write left) (gapWord d tail)
  else fromLeft (image e.target) left (pushBit e.write (gapWord d tail))

private theorem count_le_length (path : List Bool) : Control.ones path ≤ path.length := by
  induction path with
  | nil => decide
  | cons bit path ih => cases bit <;> simp [Control.ones] <;> omega

theorem donor_prefix {before : List Bool} (size : 3 ≤ before.length)
    (version : (leftCode before % 8) % 4 = 3 ∨ leftCode before % 8 = 5) :
    before = donorPrefix (leftCode before % 8) ++ before.drop (donorWidth (leftCode before % 8)) := by
  cases before with
  | nil => simp at size
  | cons first others =>
    cases others with
    | nil => simp at size
    | cons second rest =>
      cases rest with
      | nil => simp at size
      | cons third tail =>
        have form : leftCode (first :: second :: third :: tail) % 8 =
            first.toNat + 2*second.toNat + 4*third.toNat := by
          simp only [leftCode]
          cases first <;> cases second <;> cases third <;>
            simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
        rw [form] at version ⊢
        cases first <;> cases second <;> cases third <;>
          simp [donorPrefix, donorWidth] at version ⊢

structure Replayed (d : Result) (source tail : M) : Prop where
  reaches : Progress machine source (literalExit d tail)
  donorShape : donor d.node d.read = true →
    d.before = donorPrefix (leftCode d.before % 8) ++
      d.before.drop (donorWidth (leftCode d.before % 8))

theorem follow_literal (fuel : Nat) (q : Fin 344) (before input : List Bool)
    (live : 0 < height q.val) (invariant : Decoder.PrefixValid q before)
    (near : leftWindow q.val (leftCode before % 8) = true)
    {d : Result} (found : follow fuel q before input = some d) (tail : M) :
    Replayed d (cell (image q.val) (packWord before 1)
        (packWord (d.path.drop before.length) (gapWord d tail))) tail := by
  induction fuel generalizing q before input d with
  | zero => simp [follow] at found
  | succ fuel ih =>
    cases input with
    | nil => simp [follow] at found
    | cons b rest =>
      let e := transition q b
      let window := leftCode before % 8
      have checked := checked_arm q ⟨window, Nat.mod_lt _ (by decide)⟩ b live near
      by_cases internal : 0 < height e.target
      · obtain ⟨write, right, range, _, safe⟩ := Decoder.interior q b before live invariant internal
        have ordinary : special q.val b = false := by
          cases classified : special q.val b
          · rfl
          · have limit := (exceptional_target classified).2
            change 0 < height (transition q b).target at internal
            omega
        have checks : leftWindow e.target ((2*window+b.toNat)%8) = true ∧
            ordinaryCheck q.val window b = true := by
          simpa only [checkArm, show 0 < height (transition q b).target from internal,
            ↓reduceIte, ordinary, Bool.false_eq_true, Bool.and_eq_true] using checked
        have recognised : follow fuel e.target (b :: before) rest = some d := by
          simpa only [follow, q.isLt, dite_true,
            show 0 < height (transition q b).target from internal, ↓reduceIte] using found
        obtain ⟨suffix⟩ := Decoder.follow_facts fuel ⟨e.target,range⟩ _ _ internal safe recognised
        have path : before.reverse ++ (b :: suffix.scanned) = d.path := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using suffix.path
        have atHead : d.path.drop before.length = b :: suffix.scanned := by
          rw [← path, ← List.length_reverse (as := before), List.drop_append_length]
        have atNext : d.path.drop (b::before).length = suffix.scanned := by
          rw [List.length_cons, ← List.drop_drop, atHead]
          rfl
        have close := ih ⟨e.target,range⟩ (b :: before) rest internal safe
          (by rw [leftCode_mod]; exact checks.1) recognised
        rw [atHead, packWord_cons]
        have run := ordinary_run q before b (packWord suffix.scanned (gapWord d tail)) checks.2
        have progress :
            Progress machine (cell (image q.val) (packWord before 1)
              (pushBit b (packWord suffix.scanned (gapWord d tail))))
              (cell (image e.target) (packWord (b::before) 1)
                (packWord suffix.scanned (gapWord d tail))) := by
          simpa only [show (transition q b).right = true from right, ↓reduceIte,
            show (transition q b).write = b from write, packWord_cons] using run
        exact ⟨progress.trans (atNext ▸ close.reaches).reach, close.donorShape⟩
      · cases exit : Decoder.exitAt e.target with
        | none =>
          simp only [follow, q.isLt, dite_true, show ¬ 0 < height (transition q b).target from internal,
            ↓reduceIte, show Decoder.exitAt (transition q b).target = none from exit,
            Option.map_none] at found
          cases found
        | some op =>
          have result : (⟨q,before,b,rest,op⟩ : Result) = d := by
            simpa only [follow, q.isLt, dite_true, show ¬ 0 < height (transition q b).target from internal,
              ↓reduceIte, show Decoder.exitAt (transition q b).target = some op from exit,
              Option.map_some, Option.some.injEq] using found
          subst d
          have word : (before.reverse ++ [b]).drop before.length = [b] := by
            rw [← List.length_reverse (as := before), List.drop_append_length]
          simp only [Result.path, word, packWord_cons, packWord_nil]
          cases classification : special q.val b
          · have generic : ordinaryCheck q.val window b = true := by
              simpa only [checkArm, show ¬ 0 < height (transition q b).target from internal,
                ↓reduceIte, classification, Bool.false_eq_true, Bool.true_and] using checked
            have noDonor : donor q.val b = false := by
              cases b <;> simp [donor, special] at classification ⊢
              exact ⟨classification.1.2, classification.2⟩
            refine ⟨?_, fun h => by simp [noDonor] at h⟩
            simpa only [literalExit, gapWord, classification, noDonor, Bool.false_eq_true, ↓reduceIte]
              using ordinary_run q before b tail generic
          · have shape := classification
            simp only [special, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at shape
            obtain ⟨rfl, labels⟩ := shape
            by_cases owner : q.val = 48
            · have specialOwner : special 48 true = true := by decide +kernel
              have noDonor : donor q.val true = false := by simp [donor, owner]
              have port : image 8 = 8 := by decide +kernel
              have row : transition 48 true = ⟨8,false,false⟩ := by decide +kernel
              have done : ¬ 0 < height 8 := by decide +kernel
              have good : continueWordCheck window = true := by
                simpa only [checkArm, owner, row, done, ↓reduceIte, specialOwner,
                  beq_self_eq_true, Bool.true_and] using checked
              refine ⟨?_, fun h => by simp [noDonor] at h⟩
              simpa only [literalExit, gapWord, owner, specialOwner, noDonor,
                show donor 48 true = false from by decide +kernel, ↓reduceIte,
                row, port, Bool.false_eq_true] using removed_run before tail good
            · have good : donorCheck q.val window = true := by
                simpa only [checkArm, show ¬ 0 < height (transition q true).target from internal,
                  ↓reduceIte, classification, beq_iff_eq, owner, Bool.true_and] using checked
              have label : q.val = 74 ∨ q.val = 210 := by
                rcases labels with (no | d) | d
                · exact (owner no).elim
                · exact .inl d
                · exact .inr d
              have minOnes : 4 ≤ Decoder.oneBound q.val := by rcases label with h | h <;> rw [h] <;> decide +kernel
              have enough : 3 ≤ before.length := by
                have count := count_le_length before
                have limit := invariant.ones
                omega
              have windowCase := good
              simp only [donorCheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at windowCase
              have beforeSplit := donor_prefix (before := before) enough (by simpa only [window, Nat.mod_mod] using windowCase.1)
              have positive : donor q.val true = true := by
                rcases label with h | h <;> simp [donor, h]
              have run := donor_run q.val window good
                (packWord (before.drop (donorWidth window)) 1) tail
              rw [← packWord_append, ← beforeSplit] at run
              refine ⟨?_, fun _ => beforeSplit⟩
              simpa only [literalExit, gapWord, classification, positive, ↓reduceIte] using run

theorem root_replay {input : List Bool} {d : Result}
    (found : follow 70 Control.root [] input = some d) (tail : M) :
    Replayed d (cell Control.root 1 (packWord d.path (gapWord d tail))) tail := by
  have live : 0 < height Control.root := by rw [Decoder.root_shape.1]; decide
  have h := follow_literal 70 ⟨Control.root, by decide⟩ [] input live Decoder.root_shape.2
    root_left found tail
  simpa only [root_image, packWord_nil, List.length_nil, List.drop_zero] using h

theorem register_route {input : List Bool} {d : Result}
    (found : follow 70 Control.root [] input = some d)
    (facts : Decoder.Decodes Control.root [] input d) {flag : Bool} {r : Fin 11}
    (op : d.command = .register flag r) :
    RegisterRoute machine (fun dec rank => image (Decoder.registerPort dec rank)) d.path flag r := by
  have native := Stock.decoded_register_route facts op
  constructor
  · exact native.short
  · intro V _ _ tail
    have normal : special d.node d.read = false := by
      cases bit : special d.node d.read
      · rfl
      · have contra := special_command facts bit
        rw [op] at contra
        contradiction
    have normalDonor : donor d.node d.read = false := by
      cases bit : d.read <;> simp [donor,special,bit] at normal ⊢
      exact ⟨normal.1.2, normal.2⟩
    have shape := facts.leaf
    have target := facts.target
    rw [op] at shape target
    change (transition d.node d.read).target = Decoder.registerPort flag r.val at target
    have run := root_replay found tail
    simpa only [literalExit, gapWord, normal, normalDonor, Bool.false_eq_true, ↓reduceIte,
      shape.1, shape.2.1, target, Result.path, List.reverse_append, List.reverse_singleton,
      List.reverse_reverse, List.singleton_append, packWord_cons] using run.reaches

end PalomarI3334.LiteralDecoder
