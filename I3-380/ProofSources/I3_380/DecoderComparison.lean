module
public import I3_380.DecoderWindow
public import I3_380.Simulation
@[expose] public section

namespace PalomarI3380

open DecoderWindow

/-- Data for a reference-to-literal comparison. The map stores one
nine-bit literal state per reference state. Each two-bit mask specifies
the admissible predecessor bits of a reference state. Zero allows both bits. -/
structure DecoderComparison where
  reference : Machine
  physical : Machine
  stateMap : Nat
  entryMasks : Nat

namespace DecoderComparison

def state (d : DecoderComparison) (q : Nat) : Nat :=
  (d.stateMap >>> (9 * q)) % 512

def allowed (d : DecoderComparison) (q bit : Nat) : Bool :=
  let mask := (d.entryMasks >>> (2 * q)) % 4
  mask == 0 || (mask >>> bit) % 2 == 1

def translate (d : DecoderComparison) (c : Configuration) : Configuration :=
  { c with state := d.state c.state }

def translateWindow (d : DecoderComparison) (w : DecoderWindow) : DecoderWindow :=
  { w with config := d.translate w.config }

theorem translate_embed (d : DecoderComparison) (w : DecoderWindow) (l r : Nat) :
    (d.translateWindow w).embed l r = d.translate (w.embed l r) := rfl

def input (q leftBit bit : Nat) : DecoderWindow :=
  ⟨⟨q, leftBit, bit⟩, 1, 1⟩

theorem input_embed (c : Configuration) :
    (input c.state (c.left % 2) (c.right % 2)).embed (c.left / 2) (c.right / 2) = c := by
  cases c
  simp only [input, embed, Configuration.mk.injEq, true_and]
  constructor <;> omega

def validExit (d : DecoderComparison) (w : DecoderWindow) : Bool :=
  if w.leftLength = 0 then
    d.allowed w.config.state 0 && d.allowed w.config.state 1
  else d.allowed w.config.state (w.config.left % 2)

theorem validExit_sound (d : DecoderComparison) (w : DecoderWindow)
    (h : d.validExit w = true) (l r : Nat) :
    d.allowed (w.embed l r).state ((w.embed l r).left % 2) = true := by
  change d.allowed w.config.state ((w.embed l r).left % 2) = true
  by_cases hSize : w.leftLength = 0
  · simp only [validExit, hSize, ↓reduceIte, Bool.and_eq_true] at h
    have hb : (w.embed l r).left % 2 = 0 ∨ (w.embed l r).left % 2 = 1 := by omega
    rcases hb with h0 | h1
    · exact h0 ▸ h.1
    · exact h1 ▸ h.2
  · rw [embed_previous w (by omega)]
    simpa only [validExit, hSize, ↓reduceIte] using h

def checkArm (d : DecoderComparison) (q previous bit : Nat) : Bool :=
  if d.allowed q previous then
    let w := input q previous bit
    match next d.reference w with
    | none => false
    | some out =>
      decide (out.config.state ≤ d.reference.workingStates) && d.validExit out &&
        match runToMatch d.physical (d.translateWindow out) 3 (d.translateWindow w) with
        | some n => decide (0 < n)
        | none => false
  else true

def checkState (d : DecoderComparison) (q : Nat) : Bool :=
  d.checkArm q 0 0 && d.checkArm q 0 1 && d.checkArm q 1 0 && d.checkArm q 1 1

def check (d : DecoderComparison) : Bool :=
  decide (d.physical.workingStates ≤ d.state d.reference.workingStates) &&
    (List.range d.reference.workingStates).all d.checkState

def Related (d : DecoderComparison) (s c : Configuration) : Prop :=
  s.state ≤ d.reference.workingStates ∧ d.allowed s.state (s.left % 2) = true ∧
    c = d.translate s

theorem checked_arm (d : DecoderComparison) (h : d.check = true) {q : Nat}
    (inRange : q < d.reference.workingStates) (previous read : Bool) :
    d.checkArm q previous.toNat read.toNat = true := by
  simp only [check,Bool.and_eq_true] at h
  have all := h.2
  have hstate := List.all_eq_true.mp all q (List.mem_range.mpr inRange)
  simp only [checkState,Bool.and_eq_true] at hstate
  cases previous <;> cases read
  · exact hstate.1.1.1
  · exact hstate.1.1.2
  · exact hstate.1.2
  · exact hstate.2

private theorem check_arm (d : DecoderComparison) (h : d.check = true) (s : Configuration)
    (hs : s.state < d.reference.workingStates) : d.checkArm s.state (s.left % 2) (s.right % 2) = true := by
  rcases Nat.mod_two_eq_zero_or_one s.left with l | l <;>
    rcases Nat.mod_two_eq_zero_or_one s.right with r | r <;> rw [l,r]
  · exact d.checked_arm h hs false false
  · exact d.checked_arm h hs false true
  · exact d.checked_arm h hs true false
  · exact d.checked_arm h hs true true

/-- The finite two-cell comparison suffices for every step on unbounded tape. -/
theorem simulation (d : DecoderComparison) (h : d.check = true) :
    RunSimulation (step d.reference) d.physical d.Related := by
  constructor
  · intro s c hc hs
    obtain ⟨bound, _, rfl⟩ := hc
    have eq : s.state = d.reference.workingStates := by
      by_cases hne : s.state = d.reference.workingStates
      · exact hne
      · have lt : ¬ d.reference.workingStates ≤ s.state := by omega
        simp only [step, lt, ↓reduceIte] at hs
        split at hs <;> contradiction
    have terminal : d.physical.workingStates ≤ d.state d.reference.workingStates := by
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
    refine ⟨0, d.translate s, rfl, ?_⟩
    simp [step, translate, eq, terminal]
  · intro s t c hc hs
    have hq : s.state < d.reference.workingStates := by
      by_cases hlt : d.reference.workingStates ≤ s.state
      · simp [step, hlt] at hs
      · omega
    obtain ⟨_, hAllowed, rfl⟩ := hc
    let w := input s.state (s.left % 2) (s.right % 2)
    let l := s.left / 2
    let r := s.right / 2
    have hw : w.embed l r = s := input_embed s
    have hArm := d.check_arm h s hq
    simp only [checkArm, hAllowed] at hArm
    change (match next d.reference w with
       | none => false
       | some out =>
         decide (out.config.state ≤ d.reference.workingStates) && d.validExit out &&
           match runToMatch d.physical (d.translateWindow out) 3 (d.translateWindow w) with
           | some n => decide (0 < n)
           | none => false) = true at hArm
    cases href : next d.reference w with
    | none => simp [href] at hArm
    | some out =>
      cases hrun : runToMatch d.physical (d.translateWindow out) 3 (d.translateWindow w) with
      | none => simp [href, hrun] at hArm
      | some n =>
        simp only [href, hrun, Bool.and_eq_true, decide_eq_true_eq] at hArm
        have ht : out.embed l r = t :=
          Option.some.inj ((hw ▸ step_embed href l r).symm.trans hs)
        refine ⟨n, d.translate t, hArm.2, ?_, ?_, ?_, rfl⟩
        · simpa only [translate_embed, hw, ht] using runToMatch_sound hrun l r
        · rw [← ht]
          exact hArm.1.1
        · rw [← ht]
          exact d.validExit_sound out hArm.1.2 l r

theorem halts_iff (d : DecoderComparison) (h : d.check = true)
    (c : Configuration) (hc : d.Related c (d.translate c)) :
    HaltsFrom d.physical (d.translate c) ↔ HaltsFrom d.reference c :=
  (d.simulation h).halts_iff hc |>.trans (halts_iff_terminates d.reference c).symm

end DecoderComparison
end PalomarI3380
