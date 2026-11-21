module
public import I3_380.Engine.Decode
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine

/-- The leaf-specific tape and instruction-pointer facts checked at exit. -/
def LeafShape (q : Nat) (b : Bool) (before : List Bool) : Exit → Prop
  | .register _ _ =>
      (transition q b).right = true ∧ (transition q b).write = b ∧ shortZeros 0 (b :: before) = true
  | .break _ =>
      (transition q b).right = false ∧ (transition q b).write = false ∧ shortZeros 0 before = true
  | .continue skip =>
      (transition q b).right = false ∧ (transition q b).write = false ∧
        shortZeros 0 before = true ∧ (skip = true → true ∈ before)
  | .halt => (transition q b).right = true

theorem leaf_arm (q : Nat) (read : Bool) (rev : List Bool) (op : Exit)
    (hq : q < 394) (hActive : 0 < height q) (hp : PrefixValid q rev)
    (hLeaf : ¬0 < height (transition q read).target)
    (hExit : exitFor (transition q read).target = some op) : LeafShape q read rev op := by
  have h := checked_edge q read hq hActive
  simp only [checkEdge, hLeaf, ↓reduceIte, hExit] at h
  cases op with
  | register dec r =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, extend_short hp h.2⟩
  | «break» skip =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨h.1, h.2, hp.limitedZeros⟩
  | «continue» skip =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    refine ⟨h.1.1, h.1.2, hp.limitedZeros, ?_⟩
    intro hs
    subst skip
    simp only [Bool.not_true, Bool.false_or] at h
    exact hp.knownOne h.2
  | halt => exact h

/-- A decoder result records the final branch, its prefix in reverse,
and the control bits to the right of that branch. -/
structure Decoded where
  node : Nat
  before : List Bool
  read : Bool
  rest : List Bool
  command : Exit
  deriving DecidableEq, Repr

def Decoded.transition (d : Decoded) : Transition := Engine.transition d.node d.read

def Decoded.path (d : Decoded) : List Bool := d.before.reverse ++ [d.read]

def Decoded.destination (d : Decoded) (l tail : List Bool) : Configuration :=
  let e := d.transition
  if e.right then atRight e.target (e.write :: (d.before ++ l)) tail
  else atLeft e.target (d.before ++ l) (e.write :: tail)

/-- Follow read-only decoder nodes. Fuel is bounded by the verified DAG rank. -/
def follow : Nat → Nat → List Bool → List Bool → Option Decoded
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | fuel + 1, q, previous, bit :: rest =>
    let edge := transition q bit
    if 0 < height edge.target then follow fuel edge.target (bit :: previous) rest
    else (exitFor edge.target).map (fun op => ⟨q, previous, bit, rest, op⟩)

/-- A valid prefix may end at the leaf, but it never reads past a leaf. -/
def ValidPrefix (q : Nat) : List Bool → Prop
  | [] => True
  | bit :: rest => 0 < height q ∧ ValidPrefix (transition q bit).target rest

structure DecodedFrom (fuel q : Nat) (previous input scanned : List Bool) (d : Decoded) : Prop where
  computed : follow fuel q previous input = some d
  port : d.command.port = d.transition.target
  shape : LeafShape d.node d.read d.before d.command
  leaf : d.node < 394 ∧ 0 < height d.node ∧ exitFor d.transition.target = some d.command
  consumed : scanned ++ d.rest = input
  pathEq : previous.reverse ++ scanned = d.path
  lengthBound : input.length ≤ height q + d.rest.length
  validPrefix : ValidPrefix q scanned
  coversPrefix : ∀ stem tail, ValidPrefix q stem → stem ++ tail = input → stem.length ≤ scanned.length
  progress : ∀ l tail, atRight q (previous ++ l) (scanned ++ tail) ⟶+ d.destination l tail

/-- A successful walk is justified by the exact reference rows on every
possible tape continuation after the bits it used. -/
theorem follow_facts (fuel q : Nat) (previous input : List Bool)
    (hq : q < 394) (hActive : 0 < height q) (hp : PrefixValid q previous)
    {d : Decoded} (hFollow : follow fuel q previous input = some d) :
    ∃ scanned, DecodedFrom fuel q previous input scanned d := by
  induction fuel generalizing q previous input d with
  | zero => simp [follow] at hFollow
  | succ fuel ih =>
    cases input with
    | nil => simp [follow] at hFollow
    | cons b rest =>
      let e := transition q b
      have hRow : Row q b e.write e.right e.target := transition_row q b hq
      by_cases hInternal : 0 < height e.target
      · obtain ⟨hw, hd, hq', hRankRaw, hp'⟩ := internal_arm q b previous hq hActive hp hInternal
        have hRank : height e.target < height q := hRankRaw
        have hSub : follow fuel e.target (b :: previous) rest = some d := by
          simpa only [follow, show 0 < height (transition q b).target from hInternal, ↓reduceIte] using hFollow
        obtain ⟨scanned, hd'⟩ := ih e.target (b :: previous) rest hq' hInternal hp' hSub
        refine ⟨b :: scanned, ⟨hFollow, hd'.port, hd'.shape, hd'.leaf, ?_, ?_, ?_, ⟨hActive, hd'.validPrefix⟩, ?_, ?_⟩⟩
        · rw [List.cons_append, hd'.consumed]
        · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hd'.pathEq
        · have h : rest.length ≤ height e.target + d.rest.length := hd'.lengthBound
          simp only [List.length_cons]
          omega
        · intro stem tail hStem hInput
          cases stem with
          | nil => exact Nat.zero_le _
          | cons first stem =>
            simp only [List.cons_append, List.cons.injEq] at hInput
            obtain ⟨rfl, hInput⟩ := hInput
            exact Nat.succ_le_succ (hd'.coversPrefix stem tail hStem.2 hInput)
        · intro l tail
          have hr : Row q b b true e.target := by rwa [hw, hd] at hRow
          exact (right hr (previous ++ l) (scanned ++ tail)).thenReach (hd'.progress l tail).reach
      · cases hExit : exitFor e.target with
        | none =>
          simp only [follow, show ¬0 < height (transition q b).target from hInternal,
            ↓reduceIte, show exitFor (transition q b).target = none from hExit, Option.map_none] at hFollow
          contradiction
        | some command =>
          let result : Decoded := ⟨q, previous, b, rest, command⟩
          have hResult : follow (fuel + 1) q previous (b :: rest) = some result := by
            simp only [follow, show ¬0 < height (transition q b).target from hInternal,
              ↓reduceIte, show exitFor (transition q b).target = some command from hExit, Option.map_some, result]
          have hd : result = d := Option.some.inj (hResult.symm.trans hFollow)
          subst d
          refine ⟨[b], ⟨hResult, exit_port hExit, leaf_arm q b previous command hq hActive hp hInternal hExit,
            ⟨hq, hActive, hExit⟩, rfl, rfl, ?_, ⟨hActive, trivial⟩, ?_, ?_⟩⟩
          · simp only [result, List.length_cons]; omega
          · intro stem tail hStem hInput
            cases stem with
            | nil => exact Nat.zero_le _
            | cons first stem =>
              simp only [List.cons_append, List.cons.injEq] at hInput
              obtain ⟨rfl, _⟩ := hInput
              cases stem with
              | nil => exact Nat.le_refl _
              | cons second stem => exact (hInternal hStem.2.1).elim
          · intro l tail
            by_cases hDir : e.right = true
            · have hstep : Row q b e.write true e.target := hDir ▸ hRow
              simpa only [Decoded.destination, Decoded.transition, result, List.singleton_append,
                show (transition q b).right = true from hDir, ↓reduceIte] using
                right hstep (previous ++ l) tail
            · have hleft : e.right = false := Bool.of_not_eq_true hDir
              have hstep : Row q b e.write false e.target := hleft ▸ hRow
              simpa only [Decoded.destination, Decoded.transition, result, List.singleton_append,
                show (transition q b).right = false from hleft, Bool.false_eq_true, ↓reduceIte] using
                left hstep (previous ++ l) tail

theorem follow_exists (fuel q : Nat) (previous input : List Bool)
    (hq : q < 394) (hActive : 0 < height q) (hp : PrefixValid q previous)
    (hFuel : height q ≤ fuel) (hInput : height q ≤ input.length) :
    ∃ d, follow fuel q previous input = some d := by
  induction fuel generalizing q previous input with
  | zero => omega
  | succ fuel ih =>
    cases input with
    | nil => simp at hInput; omega
    | cons b rest =>
      by_cases hInternal : 0 < height (transition q b).target
      · obtain ⟨_, _, hq', hRank, hp'⟩ := internal_arm q b previous hq hActive hp hInternal
        have hLen : height (transition q b).target ≤ rest.length := by
          simp only [List.length_cons] at hInput
          omega
        simpa only [follow, hInternal, ↓reduceIte] using
          ih (transition q b).target (b :: previous) rest hq' hInternal hp' (by omega) hLen
      · have h := checked_edge q b hq hActive
        cases hexit : exitFor (transition q b).target with
        | none => simp [checkEdge, hInternal, hexit] at h
        | some op =>
          exact ⟨⟨q, previous, b, rest, op⟩, by simp only [follow, hInternal, ↓reduceIte, hexit, Option.map_some]⟩

theorem rootHeight : height Port.root = 59 := by decide +kernel

theorem decode_facts (input : List Bool) {d : Decoded}
    (h : follow 59 Port.root [] input = some d) :
    DecodedFrom 59 Port.root [] input d.path d := by
  obtain ⟨scanned, hd⟩ := follow_facts 59 Port.root [] input (by decide)
    (by rw [rootHeight]; decide) root_valid h
  have eq : scanned = d.path := hd.pathEq
  exact eq ▸ hd

theorem decode_root (input : List Bool) (longEnough : 59 ≤ input.length) :
    ∃ d, follow 59 Port.root [] input = some d :=
  follow_exists 59 Port.root [] input (by decide) (by rw [rootHeight]; decide)
    root_valid (by simpa only [rootHeight] using Nat.le_refl 59) (by rwa [rootHeight])

end PalomarI3380.Engine
