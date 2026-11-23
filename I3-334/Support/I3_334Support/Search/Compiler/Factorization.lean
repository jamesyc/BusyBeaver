module
public import I3_334Support.Search.Compiler.Optimization
@[expose] public section

namespace PalomarI3380.Compiler

def nop : Program := .op (.break_ 0)

theorem nop_closed : nop.closed := rfl

theorem executes_nop {s t : Store} {out : Flow} : Executes nop s out t ↔ out = .normal ∧ t = s := by
  constructor
  · intro execution
    cases execution
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .instruction _ _

theorem Equivalent.nop_left {p : Program} (hp : p.closed) : Equivalent (.seq nop p) p := by
  intro s out t
  rw [closed_sequence nop_closed hp]
  simp [executes_nop]

theorem Equivalent.nop_right {p : Program} (hp : p.closed) : Equivalent (.seq p nop) p := by
  intro s out t
  rw [closed_sequence hp nop_closed]
  cases out with
  | normal =>
    simp only [reduceCtorEq, false_and, false_or, executes_nop,
      true_and]
    exact ⟨fun ⟨_, h, eq⟩ => eq ▸ h, fun h => ⟨t, h, rfl⟩⟩
  | halt =>
    simp [executes_nop]
  | escape n =>
    have no (h : Executes p s (.escape n) t) : False := by
      have impossible := h.closed_flow hp
      simp at impossible
    simpa [executes_nop] using no
  | repeatAt n =>
    have no (h : Executes p s (.repeatAt n) t) : False := by
      have impossible := h.closed_flow hp
      simp at impossible
    simpa [executes_nop] using no

theorem executes_inc {r : Register} {s t : Store} {out : Flow} :
    Executes (.op (.inc r)) s out t ↔ out = .normal ∧ t = s.set r (s r + 1) := by
  constructor
  · intro execution
    cases execution
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .instruction _ _

theorem Equivalent.comm_inc (a b : Register) :
    Equivalent (.seq (.op (.inc a)) (.op (.inc b))) (.seq (.op (.inc b)) (.op (.inc a))) := by
  intro s out t
  rw [closed_sequence (p := .op (.inc a)) (q := .op (.inc b)) rfl rfl,
    closed_sequence (p := .op (.inc b)) (q := .op (.inc a)) rfl rfl]
  simp [executes_inc, increment_commute s a b]

/-- The local program laws used by normalization, independently of
whether executions have standard or model-valued lengths. -/
structure NormalizationLaws where
  equivalent : Program → Program → Prop
  reflexive : ∀ p, equivalent p p
  symmetric : ∀ {p q}, equivalent p q → equivalent q p
  transitive : ∀ {p q r}, equivalent p q → equivalent q r → equivalent p r
  sequence : ∀ {p p' q q'}, equivalent p p' → equivalent q q' → equivalent (.seq p q) (.seq p' q')
  associate : ∀ {p q r}, p.closed → q.closed → r.closed →
    equivalent (.seq (.seq p q) r) (.seq p (.seq q r))
  nopLeft : ∀ {p}, p.closed → equivalent (.seq nop p) p
  nopRight : ∀ {p}, p.closed → equivalent (.seq p nop) p
  commuteIncrements : ∀ a b,
    equivalent (.seq (.op (.inc a)) (.op (.inc b))) (.seq (.op (.inc b)) (.op (.inc a)))

def standardNormalizationLaws : NormalizationLaws where
  equivalent := Equivalent
  reflexive := Equivalent.refl
  symmetric := Equivalent.symm
  transitive := Equivalent.trans
  sequence := Equivalent.seq
  associate := reassociate
  nopLeft := Equivalent.nop_left
  nopRight := Equivalent.nop_right
  commuteIncrements := Equivalent.comm_inc

variable (laws : NormalizationLaws)

def sequence : List Program → Program
  | [] => nop
  | p :: ps => .seq p (sequence ps)

theorem sequence_closed {ps : List Program} (h : ∀ p ∈ ps, p.closed) : (sequence ps).closed := by
  induction ps with
  | nil => exact nop_closed
  | cons p ps ih =>
    exact Program.closed_seq (h p (by simp)) (ih fun q hq => h q (List.mem_cons_of_mem p hq))

theorem sequence_append {as bs : List Program}
    (ha : ∀ a ∈ as, a.closed) (hb : ∀ b ∈ bs, b.closed) :
    laws.equivalent (.seq (sequence as) (sequence bs)) (sequence (as ++ bs)) := by
  induction as with
  | nil => exact laws.nopLeft (sequence_closed hb)
  | cons a as ih =>
    have head := ha a (by simp)
    have tail : ∀ x ∈ as, Program.closed x := fun x hx => ha x (List.mem_cons_of_mem a hx)
    exact laws.transitive (laws.associate head (sequence_closed tail) (sequence_closed hb))
      (laws.sequence (laws.reflexive a) (ih tail))

/-- Order an increment within its current run. At a non-increment the
run ends, even if this operation also has no outward control effect. -/
def insertInc (r : Register) : List Program → List Program
  | .op (.inc q) :: ps =>
    if r.val ≤ q.val then .op (.inc r) :: .op (.inc q) :: ps
    else .op (.inc q) :: insertInc r ps
  | ps => .op (.inc r) :: ps

theorem mem_insertInc {p : Program} {r : Register} {ps : List Program} :
    p ∈ insertInc r ps ↔ p = .op (.inc r) ∨ p ∈ ps := by
  induction ps with
  | nil => simp [insertInc]
  | cons q ps ih =>
    cases q with
    | seq => simp [insertInc]
    | op q =>
      cases q <;> simp only [insertInc, List.mem_cons]
      split
      · simp only [List.mem_cons]
      · simp only [ih, List.mem_cons, or_left_comm]

theorem insertInc_sound (r : Register) {ps : List Program} (h : ∀ p ∈ ps, p.closed) :
    laws.equivalent (sequence (.op (.inc r) :: ps)) (sequence (insertInc r ps)) := by
  induction ps with
  | nil => exact laws.reflexive _
  | cons p ps ih =>
    cases p with
    | seq => exact laws.reflexive _
    | op op =>
      cases op <;> try exact laws.reflexive _
      rename_i q
      unfold insertInc
      split
      · exact laws.reflexive _
      · have tail : ∀ a ∈ ps, a.closed := fun a ha => h a (List.mem_cons_of_mem _ ha)
        have closed := sequence_closed tail
        exact laws.transitive
          (laws.symmetric (laws.associate (p := .op (.inc r)) (q := .op (.inc q)) rfl rfl closed))
          (laws.transitive (laws.sequence (laws.commuteIncrements r q) (laws.reflexive _))
            (laws.transitive (laws.associate (p := .op (.inc q)) (q := .op (.inc r)) rfl rfl closed)
              (laws.sequence (laws.reflexive _) (ih tail))))

def orderIncrements : List Program → List Program
  | [] => []
  | .op (.inc r) :: ps => insertInc r (orderIncrements ps)
  | p :: ps => p :: orderIncrements ps

theorem orderIncrements_sound {ps : List Program} (h : ∀ p ∈ ps, p.closed) :
    (∀ p ∈ orderIncrements ps, p.closed) ∧
      laws.equivalent (sequence ps) (sequence (orderIncrements ps)) := by
  induction ps with
  | nil => exact ⟨h, laws.reflexive _⟩
  | cons p ps ih =>
    obtain ⟨closed, ev⟩ := ih fun a ha => h a (List.mem_cons_of_mem p ha)
    have prepend :
        (∀ a ∈ p :: orderIncrements ps, Program.closed a) ∧
          laws.equivalent (sequence (p :: ps)) (sequence (p :: orderIncrements ps)) := by
      refine ⟨fun a ha => ?_, laws.sequence (laws.reflexive p) ev⟩
      rcases List.mem_cons.mp ha with rfl | ht
      · exact h a List.mem_cons_self
      · exact closed a ht
    cases p with
    | seq => exact prepend
    | op op =>
      cases op <;> try exact prepend
      rename_i r
      refine ⟨fun a ha => prepend.1 a (List.mem_cons.mpr (mem_insertInc.mp ha)), ?_⟩
      exact laws.transitive prepend.2 (insertInc_sound laws r closed)

inductive Layout where
  | atom (p : Program)
  | block (parts : List Program)

def Layout.render : Layout → Program
  | .atom p => p
  | .block ps => sequence (orderIncrements ps)

def Layout.parts : Layout → List Program
  | .atom (.op (.break_ 0)) => []
  | .atom p => [p]
  | .block ps => ps

def Layout.assemble (p q : Nat × Nat) : Nat × Nat :=
  (max (p.1 - 1) q.1, max p.2 (q.2 - 1))

def layout : Program → (Nat × Nat) × Layout
  | .op op => ((Program.op op).needs, .atom (.op op))
  | .seq p q =>
    let (np, lp) := layout p
    let (nq, lq) := layout q
    (Layout.assemble np nq,
      if np == (0, 0) && nq == (0, 0) then .block (lp.parts ++ lq.parts)
      else .atom (.seq lp.render lq.render))

def Layout.Valid (p : Program) (l : Layout) : Prop :=
  laws.equivalent p l.render ∧
    (p.closed → (∀ q ∈ l.parts, q.closed) ∧ laws.equivalent p (sequence l.parts))

private theorem Layout.atom_valid {p q : Program} (needs : p.needs = q.needs) (h : laws.equivalent p q) :
    Layout.Valid laws p (.atom q) := by
  refine ⟨h, fun hp => ?_⟩
  have closed : q.closed := needs.symm.trans hp
  have single (hs : (Layout.atom q).parts = [q]) :
      (∀ t ∈ (Layout.atom q).parts, t.closed) ∧ laws.equivalent p (sequence (Layout.atom q).parts) := by
    rw [hs]
    exact ⟨fun r hr => (List.mem_singleton.mp hr).symm ▸ closed, laws.transitive h (laws.symmetric (laws.nopRight closed))⟩
  cases q with
  | seq => exact single rfl
  | op op =>
    cases op with
    | break_ n =>
      cases n with
      | zero => exact ⟨fun _ hn => (List.not_mem_nil hn).elim, h⟩
      | succ n => exact single rfl
    | inc | decNZ | continue_ | halt => exact single rfl

private theorem layout_sound (p : Program) :
    (layout p).1 = p.needs ∧ (layout p).2.Valid laws p ∧ (layout p).2.render.needs = p.needs := by
  induction p with
  | op op => exact ⟨rfl, Layout.atom_valid laws rfl (laws.reflexive _), rfl⟩
  | seq p q ihp ihq =>
    have needs : Layout.assemble (layout p).1 (layout q).1 = (Program.seq p q).needs := by
      rw [ihp.1, ihq.1]
      rfl
    by_cases both : ((layout p).1 == (0, 0) && (layout q).1 == (0, 0)) = true
    · have checks : ((layout p).1 == (0, 0)) = true ∧ ((layout q).1 == (0, 0)) = true := by
        simpa only [Bool.and_eq_true] using both
      have hp : p.closed := ihp.1.symm.trans (eq_of_beq checks.1)
      have hq : q.closed := ihq.1.symm.trans (eq_of_beq checks.2)
      obtain ⟨partsP, relationshipP⟩ := ihp.2.1.2 hp
      obtain ⟨partsQ, relationshipQ⟩ := ihq.2.1.2 hq
      let parts := (layout p).2.parts ++ (layout q).2.parts
      have closed : ∀ r ∈ parts, Program.closed r := fun r hr =>
        (List.mem_append.mp hr).elim (partsP r) (partsQ r)
      have equiv := laws.transitive (laws.sequence relationshipP relationshipQ) (sequence_append laws partsP partsQ)
      have ordered := orderIncrements_sound laws closed
      have zero := Program.closed_seq hp hq
      simp only [layout, both, ↓reduceIte]
      exact ⟨needs, ⟨laws.transitive equiv ordered.2, fun _ => ⟨closed, equiv⟩⟩,
        (sequence_closed ordered.1).trans zero.symm⟩
    · have renderedNeeds :
          (Program.seq (layout p).2.render (layout q).2.render).needs = (Program.seq p q).needs := by
        simp only [Program.needs, ihp.2.2, ihq.2.2]
      simp only [layout, both]
      exact ⟨needs, Layout.atom_valid laws renderedNeeds.symm (laws.sequence ihp.2.1.1 ihq.2.1.1), renderedNeeds⟩

/-- Normalize maximal closed sequences, leaving all unconsumed jump
counts unchanged. Sorting occurs once per maximal block. -/
def normalize (p : Program) : Program := (layout p).2.render

theorem normalize_sound (p : Program) : laws.equivalent p (normalize p) :=
  (layout_sound laws p).2.1.1

theorem normalize_needs (p : Program) : (normalize p).needs = p.needs :=
  (layout_sound standardNormalizationLaws p).2.2

theorem equivalent_under_laws {p q : Program} (h : normalize p = normalize q) : laws.equivalent p q :=
  laws.transitive (normalize_sound laws p) (h ▸ laws.symmetric (normalize_sound laws q))

theorem equivalent_of_normalized {p q : Program} (h : normalize p = normalize q) : Equivalent p q :=
  equivalent_under_laws standardNormalizationLaws h

/-- Structural equality checks only constructors and the small operation
payloads. This keeps the computation separate from the equality proof. -/
def sameProgram : Program → Program → Bool
  | .op p, .op q => decide (p = q)
  | .seq a b, .seq c d => sameProgram a c && sameProgram b d
  | _, _ => false

theorem sameProgram_sound {p q : Program} (h : sameProgram p q = true) : p = q := by
  induction p generalizing q with
  | op p =>
    cases q with
    | op q => exact congrArg Program.op (of_decide_eq_true h)
    | seq => cases h
  | seq p r ihp ihr =>
    cases q with
    | op => cases h
    | seq q s =>
      simp only [sameProgram, Bool.and_eq_true] at h
      rw [ihp h.1, ihr h.2]

end PalomarI3380.Compiler
