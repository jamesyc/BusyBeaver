module
public import I3_334Support.Search.Compiler.Program
@[expose] public section

namespace PalomarI3380.Compiler

def Equivalent (p q : Program) : Prop :=
  ∀ s out t, Executes p s out t ↔ Executes q s out t

theorem Equivalent.refl (p : Program) : Equivalent p p := fun _ _ _ => Iff.rfl
theorem Equivalent.symm {p q : Program} (h : Equivalent p q) : Equivalent q p :=
  fun s out t => (h s out t).symm
theorem Equivalent.trans {p q r : Program} (h : Equivalent p q) (k : Equivalent q r) :
    Equivalent p r := fun s out t => (h s out t).trans (k s out t)

private theorem seq_transfer {p p' q q' : Program} (left : Equivalent p p') (right : Equivalent q q')
    {tree : Program} {s t : Store} {out : Flow}
    (execution : Executes tree s out t) (shape : tree = .seq p q) :
    Executes (.seq p' q') s out t := by
  induction execution with
  | instruction => cases shape
  | leftExit e next _ =>
    cases shape
    exact .leftExit ((left _ _ _).mp e) next
  | rightExit e₁ e₂ next _ _ =>
    cases shape
    exact .rightExit ((left _ _ _).mp e₁) ((right _ _ _).mp e₂) next
  | reenter e₁ e₂ e₃ _ _ ih =>
    cases shape
    exact .reenter ((left _ _ _).mp e₁) ((right _ _ _).mp e₂) (ih rfl)

theorem Equivalent.seq {p p' q q' : Program} (left : Equivalent p p') (right : Equivalent q q') :
    Equivalent (.seq p q) (.seq p' q') := fun _ _ _ =>
  ⟨fun execution => seq_transfer left right execution rfl,
   fun execution => seq_transfer left.symm right.symm execution rfl⟩

theorem closed_sequence {p q : Program} (hp : p.closed) (hq : q.closed)
    (s : Store) (out : Flow) (t : Store) :
    Executes (.seq p q) s out t ↔
      (out = .halt ∧ Executes p s .halt t) ∨
        ∃ middle, Executes p s .normal middle ∧ Executes q middle out t := by
  constructor
  · intro execution
    cases execution with
    | leftExit h next =>
      rcases h.closed_flow hp with same | same
      · simp [same, Flow.fromLeft] at next
      · simp only [same, Flow.fromLeft, Option.some.injEq] at next
        exact Or.inl ⟨next.symm, same ▸ h⟩
    | rightExit h₁ h₂ next =>
      rcases h₂.closed_flow hq with same | same <;>
        simp only [same, Flow.fromRight, Option.some.injEq] at next
      · exact Or.inr ⟨_, h₁, next ▸ (same ▸ h₂)⟩
      · exact Or.inr ⟨_, h₁, next ▸ (same ▸ h₂)⟩
    | reenter _ h₂ _ =>
      have impossible := h₂.closed_flow hq
      simp at impossible
  · rintro (⟨rfl, h⟩ | ⟨middle, h₁, h₂⟩)
    · exact .leftExit h rfl
    · rcases h₂.closed_flow hq with rfl | rfl
      · exact .rightExit h₁ h₂ rfl
      · exact .rightExit h₁ h₂ rfl

/-- Reassociation does not move any break or continue across its owner
when all three subprograms are closed. -/
theorem reassociate {p q r : Program} (hp : p.closed) (hq : q.closed) (hr : r.closed) :
    Equivalent (.seq (.seq p q) r) (.seq p (.seq q r)) := by
  intro s out t
  rw [closed_sequence (Program.closed_seq hp hq) hr, closed_sequence hp (Program.closed_seq hq hr)]
  constructor
  · rintro (⟨rfl, halted⟩ | ⟨afterBoth, both, last⟩)
    · rcases (closed_sequence hp hq s .halt t).mp halted with ⟨_, first⟩ | ⟨next, first, second⟩
      · exact Or.inl ⟨rfl, first⟩
      · exact Or.inr ⟨next, first, .leftExit second rfl⟩
    · rcases (closed_sequence hp hq s .normal afterBoth).mp both with ⟨impossible, _⟩ | ⟨next, first, second⟩
      · cases impossible
      · exact Or.inr ⟨next, first, (closed_sequence hq hr next out t).mpr
          (Or.inr ⟨afterBoth, second, last⟩)⟩
  · rintro (⟨rfl, first⟩ | ⟨next, first, both⟩)
    · exact Or.inl ⟨rfl, .leftExit first rfl⟩
    · rcases (closed_sequence hq hr next out t).mp both with ⟨rfl, second⟩ | ⟨afterBoth, second, last⟩
      · exact Or.inl ⟨rfl, .rightExit first second rfl⟩
      · exact Or.inr ⟨afterBoth, .rightExit first second rfl, last⟩

theorem increment_commute {V : Type} [OfNat V 1] [Add V] (s : Store V) (a b : Register) :
    (s.set a (s a + 1)).set b ((s.set a (s a + 1)) b + 1) =
      (s.set b (s b + 1)).set a ((s.set b (s b + 1)) a + 1) := by
  by_cases same : a = b
  · cases same; rfl
  · funext i
    by_cases ha : i = a <;> by_cases hb : i = b <;> simp [Store.set, ha, hb, same, Ne.symm same]

end PalomarI3380.Compiler
