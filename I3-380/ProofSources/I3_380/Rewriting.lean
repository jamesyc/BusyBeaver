module
public import I3_380.Ground
@[expose] public section

namespace PalomarI3380

/-- One level of a ground term context, with exactly one open argument. -/
inductive Frame where
  | neg | converse | choice | localRel
  | nandLeft (right : ClosedTerm) | nandRight (left : ClosedTerm)
  | productLeft (right : ClosedTerm) | productRight (left : ClosedTerm)
  | nodeFirst (second third : ClosedTerm)
  | nodeSecond (first third : ClosedTerm)
  | nodeThird (first second : ClosedTerm)

def Frame.fill : Frame → ClosedTerm → ClosedTerm
  | .neg, x => .neg x
  | .converse, x => .converse x
  | .choice, x => .choice x
  | .localRel, x => .localRel x
  | .nandLeft y, x => .nand x y
  | .nandRight x, y => .nand x y
  | .productLeft y, x => .product x y
  | .productRight x, y => .product x y
  | .nodeFirst y z, x => .node x y z
  | .nodeSecond x z, y => .node x y z
  | .nodeThird x y, z => .node x y z

theorem Derives.underFrame {E : List Equation} {a b : ClosedTerm}
    (h : Derives E a b) (f : Frame) : Derives E (f.fill a) (f.fill b) := by
  cases f <;> first
    | exact .neg h
    | exact .converse h
    | exact .choice h
    | exact .localRel h
    | exact .nand h (.refl _)
    | exact .nand (.refl _) h
    | exact .product h (.refl _)
    | exact .product (.refl _) h
    | exact .node h (.refl _) (.refl _)
    | exact .node (.refl _) h (.refl _)
    | exact .node (.refl _) (.refl _) h

/-- Replace one subterm by an instance of one equation, in either direction. -/
inductive Replacement (E : List Equation) : ClosedTerm → ClosedTerm → Prop where
  | forward {e : Equation} : e ∈ E → (σ : Fin 3 → ClosedTerm) →
      Replacement E (e.1.subst σ) (e.2.subst σ)
  | backward {e : Equation} : e ∈ E → (σ : Fin 3 → ClosedTerm) →
      Replacement E (e.2.subst σ) (e.1.subst σ)
  | under (f : Frame) : Replacement E a b → Replacement E (f.fill a) (f.fill b)

theorem Replacement.symm {E : List Equation} {a b : ClosedTerm} (h : Replacement E a b) :
    Replacement E b a := by
  induction h with
  | forward he σ => exact .backward he σ
  | backward he σ => exact .forward he σ
  | under f _ ih => exact .under f ih

theorem Replacement.derives {E : List Equation} {a b : ClosedTerm} (h : Replacement E a b) :
    Derives E a b := by
  induction h with
  | forward he σ => exact .instanceOf he σ
  | backward he σ => exact .symm (.instanceOf he σ)
  | under f _ ih => exact ih.underFrame f

/-- A finite sequence of ground replacements of the kind the machine enumerates. -/
inductive RewriteChain (E : List Equation) : ClosedTerm → ClosedTerm → Prop where
  | nil (a) : RewriteChain E a a
  | snoc : RewriteChain E a b → Replacement E b c → RewriteChain E a c

namespace RewriteChain

theorem single {E : List Equation} {a b : ClosedTerm} (h : Replacement E a b) :
    RewriteChain E a b := .snoc (.nil _) h

theorem append {E : List Equation} {a b c : ClosedTerm}
    (p : RewriteChain E a b) (q : RewriteChain E b c) : RewriteChain E a c := by
  induction q with
  | nil => exact p
  | snoc _ s ih => exact .snoc ih s

theorem reverse {E : List Equation} {a b : ClosedTerm} (h : RewriteChain E a b) :
    RewriteChain E b a := by
  induction h with
  | nil => exact .nil _
  | snoc _ s ih => exact (single s.symm).append ih

theorem underFrame {E : List Equation} {a b : ClosedTerm}
    (h : RewriteChain E a b) (f : Frame) : RewriteChain E (f.fill a) (f.fill b) := by
  induction h with
  | nil => exact .nil _
  | snoc _ s ih => exact .snoc ih (.under f s)

theorem derives {E : List Equation} {a b : ClosedTerm} (h : RewriteChain E a b) :
    Derives E a b := by
  induction h with
  | nil => exact .refl _
  | snoc _ s ih => exact ih.trans s.derives

end RewriteChain

theorem Derives.rewriteChain {E : List Equation} {a b : ClosedTerm} (h : Derives E a b) :
    RewriteChain E a b := by
  induction h with
  | instanceOf he σ => exact .single (.forward he σ)
  | refl => exact .nil _
  | symm _ ih => exact ih.reverse
  | trans _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | neg _ ih => exact ih.underFrame .neg
  | converse _ ih => exact ih.underFrame .converse
  | choice _ ih => exact ih.underFrame .choice
  | localRel _ ih => exact ih.underFrame .localRel
  | nand h₁ h₂ ih₁ ih₂ =>
      exact (ih₁.underFrame (.nandLeft _)).append (ih₂.underFrame (.nandRight _))
  | product h₁ h₂ ih₁ ih₂ =>
      exact (ih₁.underFrame (.productLeft _)).append (ih₂.underFrame (.productRight _))
  | node h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
      exact ((ih₁.underFrame (.nodeFirst _ _)).append
        (ih₂.underFrame (.nodeSecond _ _))).append (ih₃.underFrame (.nodeThird _ _))

theorem acceptance_chain_iff :
    RewriteChain Manifest.final (.const .D) (.const .J) ↔
      Derives Manifest.preceding (.const .D) (.const .J) :=
  ⟨fun h => Derives.acceptance_iff.mp h.derives,
   fun h => (Derives.acceptance_iff.mpr h).rewriteChain⟩

end PalomarI3380
