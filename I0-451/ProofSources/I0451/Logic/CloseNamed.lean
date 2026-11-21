module
public import I0451.Logic.NamedTranslation
public import I0451.Omega.NativeTheories

/-! Close a named formula by quantifying its finite list of names.
This connects the externally named axioms with closed sentences of
the set-language proof calculus. -/
@[expose] public section
namespace I0451.Logic.NamedFormula

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open I0451.Arithmetization I0451.Logic.Tait
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZF207.CKernel.Generic

noncomputable def freeLabels (f : NamedFormula) : List Nat :=
  NamedFormula.rec (motive := fun _ => List Nat) [] []
    (fun a b => [a,b]) (fun a b => [a,b])
    (fun _ _ a b => a ++ b) (fun x _ a => a.filter (· != x)) f

@[simp] theorem freeLabels_all {i x : Nat} {f : NamedFormula} :
    i ∈ (.all x f : NamedFormula).freeLabels ↔ i ∈ f.freeLabels ∧ i ≠ x := by
  simp [freeLabels]

def closeOver (labels : List Nat) (f : NamedFormula) : NamedFormula :=
  labels.foldr NamedFormula.all f

theorem closeOver_freeLabels {i : Nat} (names : List Nat) (f : NamedFormula) :
    i ∈ (f.closeOver names).freeLabels ↔ i ∈ f.freeLabels ∧ i ∉ names := by
  induction names with
  | nil => simp [closeOver]
  | cons x xs ih =>
    simp only [closeOver, List.foldr_cons, freeLabels_all]
    change (i ∈ (f.closeOver xs).freeLabels ∧ i ≠ x) ↔ _
    rw [ih, List.mem_cons, not_or]
    tauto

theorem freeLabel_is_label {f : NamedFormula} {i : Nat} (member : i ∈ f.freeLabels) :
    i ∈ f.labels := by
  induction f with
  | imp a b ha hb =>
    rcases List.mem_append.mp member with left | right
    · exact List.mem_append_left _ (ha left)
    · exact List.mem_append_right _ (hb right)
  | all x f ih => exact List.mem_cons_of_mem _ (ih (freeLabels_all.mp member).1)
  | _ => exact member

theorem closed_names (f : NamedFormula) (x : Nat) :
    x ∉ (f.closeOver f.labels).freeLabels := by
  rw [closeOver_freeLabels]
  exact fun h => h.2 (freeLabel_is_label h.1)

theorem relabel_free_congr {names s t : Nat → Nat} {d : Nat} (f : NamedFormula)
    (agree : ∀ i ∈ f.freeLabels, s i = t i) : f.relabel names d s = f.relabel names d t := by
  induction f generalizing d s t with
  | truth | falsity => rfl
  | mem x y | equal x y =>
    simp only [relabel]
    rw [agree x (by simp [freeLabels]), agree y (by simp [freeLabels])]
  | imp a b ha hb =>
    simp only [relabel]
    rw [ha (fun i h => agree i (List.mem_append_left _ h)),
      hb (fun i h => agree i (List.mem_append_right _ h))]
  | all x f ih =>
    simp only [relabel]
    apply congrArg (NamedFormula.all _)
    apply ih
    intro i used
    by_cases bound : i = x
    · simp [assign, bound]
    · simp [assign, bound, agree i (freeLabels_all.mpr ⟨used,bound⟩)]

private theorem toSet_free_label {n : Nat} (f : NamedFormula) (terms : Nat → SyntacticSemiterm ℒₛₑₜ n)
    {x : Nat} (appears : (f.toSet terms).FVar? x) : ∃ i ∈ f.freeLabels, (terms i).FVar? x := by
  induction f generalizing n terms with
  | truth => simp [toSet] at appears
  | falsity => simp [toSet] at appears
  | mem a b | equal a b =>
    obtain ⟨i, hit⟩ := Semiformula.fvar?_rel.mp appears
    have either : i = 0 ∨ i = 1 := by omega
    rcases either with rfl | rfl
    · exact ⟨a, by simp [freeLabels], hit⟩
    · exact ⟨b, by simp [freeLabels], hit⟩
  | imp a b ha hb =>
    simp only [toSet, Semiformula.imp_eq, Semiformula.fvar?_or, Semiformula.FVar?, Semiformula.freeVariables_not] at appears
    rcases appears with left | right
    · obtain ⟨i, mem, hit⟩ := ha terms left
      exact ⟨i, List.mem_append_left _ mem, hit⟩
    · obtain ⟨i, mem, hit⟩ := hb terms right
      exact ⟨i, List.mem_append_right _ mem, hit⟩
  | all a f ih =>
    simp only [toSet, Semiformula.fvar?_all] at appears
    obtain ⟨i, used, inTerm⟩ := ih (SetSyntax.bindTerms terms a) appears
    have differs : i ≠ a := by
      intro same
      simp [SetSyntax.bindTerms, same] at inTerm
    refine ⟨i, freeLabels_all.mpr ⟨used,differs⟩, ?_⟩
    simp only [SetSyntax.bindTerms, differs, ite_false] at inTerm
    cases ht : terms i with
    | bvar j => simp [ht] at inTerm
    | fvar z => simpa [ht] using inTerm
    | func r a => exact nomatch r

theorem closeOver_provable (f : NamedFormula) (names : List Nat) (proof : NativeDerivable f.code) :
    NativeDerivable (f.closeOver names).code := by
  induction names with
  | nil => exact proof
  | cons a names ih => exact NativeDerivable.generalize a ih

theorem closedFormula_noFree (f : NamedFormula) :
    ((f.closeOver f.labels).toSet (fun i => (Semiterm.fvar i : SyntacticTerm ℒₛₑₜ))).freeVariables = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x used
  obtain ⟨i,found,_⟩ := toSet_free_label (f.closeOver f.labels)
    (fun i => Semiterm.fvar i) used
  exact f.closed_names i found

def closedSentence (f : NamedFormula) : SetTheorySentence :=
  ((f.closeOver f.labels).toSet (fun i => Semiterm.fvar i)).toEmpty f.closedFormula_noFree

theorem closedSentence_emb (f : NamedFormula) :
    (Rewriting.emb f.closedSentence : SetTheoryProposition) =
      (f.closeOver f.labels).toSet (fun i => Semiterm.fvar i) :=
  Semiformula.emb_toEmpty _ _

private theorem label_le_max {x : Nat} {list : List Nat} (present : x ∈ list) :
    x ≤ list.foldr max 0 := by
  induction list with
  | nil => simp at present
  | cons y ys ih =>
    rcases List.mem_cons.mp present with rfl | inTail
    · exact le_max_left _ _
    · exact le_trans (ih inTail) (le_max_right _ _)

private theorem relabel_shift (f : NamedFormula) (names : Nat → Nat) (base d : Nat) (s : Nat → Nat) :
    f.relabel (fun i => names (base + i)) d s = f.relabel names (base + d) s := by
  induction f generalizing d s with
  | imp a b ha hb => simp only [relabel, ha, hb]
  | all x f ih => simp only [relabel, ih, Nat.add_assoc]
  | _ => rfl

attribute [local irreducible] tr chiS modelImp I0451.Runtime.modelTag

set_option maxHeartbeats 500000 in
private theorem standardizeAtFreshDepth (p : NamedFormula) (proof : NativeDerivable p.code) :
    NativeDerivable (p.relabel (xlab 1) (p.labels.foldr max 0 + 1) id).code := by
  let bound := p.labels.foldr max 0 + 1
  let names (i : Nat) := xlab (1 : Nat) (bound + i)
  have distinct : Function.Injective names := by
    intro a b equal
    have hh := (xlab_inj.mp equal).2
    omega
  have fresh (i : Nat) : names i ∉ p.labels := by
    intro old
    have earlier := label_le_max old
    have later : bound + i < names i := by
      exact lt_xlab 1 (bound + i)
    dsimp [bound] at later
    omega
  have norm := p.standardize_provable names 0 distinct fresh
  rw [p.standardize_eq_relabel names 0 fresh, relabel_shift, Nat.add_zero] at norm
  show NativeDerivable (p.relabel (xlab 1) bound id).code
  exact (Logic.Ctx.iffMp (S := calculus.toLogic) (.thm norm) (.thm proof)).empty


set_option maxHeartbeats 700000 in
theorem closedSentence_compiles (f : NamedFormula) (proof : NativeDerivable f.code) :
    NativeDerivable (chiS 0 (⌜f.closedSentence⌝ : Nat)) := by
  let p := f.closeOver f.labels
  let body := p.toSet (fun i => (Semiterm.fvar i : SyntacticTerm ℒₛₑₜ))
  let bound := p.labels.foldr max 0 + 1
  have normProof : NativeDerivable (p.relabel (xlab 1) bound id).code :=
    standardizeAtFreshDepth p (f.closeOver_provable f.labels proof)
  have same : p.relabel (xlab 1) bound id =
      p.relabel (xlab 1) bound (termLabel 0 0 ∘ fun i => (Semiterm.fvar i : SyntacticTerm ℒₛₑₜ)) :=
    p.relabel_free_congr (fun i used => (f.closed_names i used).elim)
  rw [same] at normProof
  have compiler := p.native_lowering (fun i => (Semiterm.fvar i : SyntacticTerm ℒₛₑₜ)) 0 0 bound 1
  have shifted : NativeDerivable (π₁ (tr ⟪0,bound,0,1⟫ (⌜body⌝ : Nat))) :=
    (Logic.Ctx.iffMpr (S := calculus.toLogic) (.thm compiler) (.thm normProof)).empty
  have wf := (Semiformula.quote_isSemiformula (V := Nat) body).isUFormula
  have alpha := native_alpha wf bound
  rw [Sentence.quote_def, f.closedSentence_emb, chiS]
  exact (Logic.Ctx.iffMpr (S := calculus.toLogic) (.thm alpha) (.thm shifted)).empty

theorem closedSentence_provable (f : NamedFormula) (proof : NativeDerivable f.code) :
    I0451.Omega.nativeSetTheory ⊢ f.closedSentence :=
  I0451.Omega.nativeSet_theorem_of_compiled (f.closedSentence_compiles proof)

end I0451.Logic.NamedFormula
