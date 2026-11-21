module
public import I0451.Logic.TruthRelativization
public import I0451.Logic.CodedElementarity

/-! Preserve internally coded elementarity when restricting the
assignment graph to a fixed transitive member of its domain. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode I0451.Logic.ZFModel I0451.Logic.SetFormulaPrograms

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

theorem ReadsTuple.prepend {j M args images longer longerImages : V}
    (reads : ReadsTuple j args images) (natural : lh args ∈ (ω : V)) (fixed : At E j M M)
    (argument : Prepends M args longer) (image : Prepends M images longerImages) :
    ReadsTuple j longer longerImages := by
  refine ⟨image.sequence, by rw [argument.length, image.length, reads.length], ?_⟩
  intro i inside
  rw [argument.length] at inside
  rcases (cases_mem_succ_nat natural).2 i inside with head | ⟨slot, earlier, tail⟩
  · subst i
    rw [argument.head, image.head]
    exact fixed
  · subst i
    rw [argument.tail slot earlier, image.tail slot (reads.length.symm ▸ earlier)]
    exact reads.each slot earlier

theorem CodedElementary.restrict {D M j h : V} (large : CodedElementary D j)
    (transitive : IsTransitive M) (within : M ⊆ D) (named : M ∈ D) (fixed : At E j M M)
    (valid : h ∈ assignments M)
    (restricts : ∀ x ∈ M, ∀ y, At E h x y → At E j x y) : CodedElementary M h := by
  refine ⟨valid, fun word wf index inside args tuple images applies => ?_⟩
  obtain ⟨translated, compiled⟩ := relativizedWord_exists word
  have natural := (wf.2.2 index inside).1
  have argsNat : lh args ∈ (ω : V) := tuple.2.1.symm ▸ natural
  have imagesNat : lh images ∈ (ω : V) := applies.length.symm ▸ argsNat
  have imageTuple : Tuple M images (nodeArity word index) :=
    ⟨applies.sequence, applies.length.trans tuple.2.1, applies.range_subset valid tuple.1 tuple.2.2⟩
  obtain ⟨longer, inserted⟩ := prepends_exists M args argsNat
  obtain ⟨longerImages, mapped⟩ := prepends_exists M images imagesNat
  have newArgs := inserted.tuple ⟨tuple.1, tuple.2.1, subset_trans tuple.2.2 within⟩ natural named
  rw [← compiled.arity inside] at newArgs
  have agrees : ReadsTuple j args images :=
    ⟨applies.sequence, applies.length, fun k kIn =>
      restricts _ (tuple.2.2 _ (mem_range_iff.mpr ⟨k, tuple.1.znth kIn⟩)) _ (applies.each k kIn)⟩
  have relativeTruth := large.2 translated (compiled.wellFormed wf) index (compiled.length.symm ▸ inside)
    longer newArgs longerImages (agrees.prepend argsNat fixed inserted mapped)
  have before := relativized_satisfaction transitive within named wf compiled inside tuple inserted
  have after := relativized_satisfaction transitive within named wf compiled inside imageTuple mapped
  exact before.trans (relativeTruth.trans after.symm)

noncomputable def restrictedGraph (j M : V) : V :=
  sep (M ×ˢ M) (fun p => ∃ x y, p = ⟨x,y⟩ₖ ∧ At E j x y) (by
    have atCodes := At_definable (V := V)
    definability)

theorem restrictedGraph_at (j M x y : V) :
    At E (restrictedGraph j M) x y ↔ x ∈ M ∧ y ∈ M ∧ At E j x y := by
  rw [at_iff_mem_kpair, restrictedGraph, mem_sep_iff]
  constructor
  · rintro ⟨within, a, b, equal, value⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj equal
    rcases mem_prod_iff.mp within with ⟨i, iIn, k, kIn, same⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj same
    exact ⟨iIn, kIn, value⟩
  · rintro ⟨xIn, yIn, value⟩
    exact ⟨mem_prod_iff.mpr ⟨x, xIn, y, yIn, rfl⟩, x, y, rfl, value⟩

theorem restrictedGraph_mem {D M j : V} (jD : j ∈ assignments D)
    (inside : M ⊆ D) (preserves : ∀ x ∈ M, ∀ y, At E j x y → y ∈ M) :
    restrictedGraph j M ∈ assignments M := by
  apply (mem_universe _ _).mpr
  constructor
  · intro p pIn s sIn x xIn
    have product : p ∈ M ×ˢ M := (mem_sep_iff.mp pIn).1
    obtain ⟨u, uIn, v, vIn, rfl⟩ := mem_prod_iff.mp product
    have shape := (kpair_is_pair u v) s
    exact ((shape.mp sIn).2 x xIn).elim (fun eq => eq.symm ▸ uIn) (fun eq => eq.symm ▸ vIn)
  · intro x
    let outside : Domain E D := ⟨x.val, inside x.val x.property⟩
    obtain ⟨y, given, unique⟩ := ((mem_universe _ _).mp jD).2 outside
    refine ⟨y, (restrictedGraph_at _ _ _ _).mpr ⟨x.property, preserves x.val x.property y given, given⟩, ?_⟩
    intro z read
    exact unique z ((restrictedGraph_at _ _ _ _).mp read).2.2

theorem CodedElementary.restrictGraph {D M j : V} (large : CodedElementary D j)
    (transitive : IsTransitive M) (within : M ⊆ D) (named : M ∈ D) (fixed : At E j M M)
    (preserves : ∀ x ∈ M, ∀ y, At E j x y → y ∈ M) :
    CodedElementary M (restrictedGraph j M) :=
  large.restrict transitive within named fixed (restrictedGraph_mem large.1 within preserves)
    (fun x _ y read => ((restrictedGraph_at _ _ x y).mp read).2.2)

end I0451.Logic.SetAssignments
