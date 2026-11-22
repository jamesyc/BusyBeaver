module
public import ZF192Support.Calculus.Gate.Assignments
public import ZF192Support.Calculus.Gate.Code
public import ZF192Support.SetTheory.Hulls.ScottHull
@[expose] public section

namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open CCodeSoundness

theorem named_eval_definable {V : Type*} [SetStructure V]
 (A : CCodeSoundness.Formula) {k : Nat} (s : Nat → (Fin k → V) → V)
 (hs : ∀ i, Language.DefinableFunction (L := Language.set) (s i)) :
 Language.Definable (L := Language.set) (fun v => A.eval (fun x y : V => x ∈ y) (fun i => s i v)) := by
 induction A generalizing k with
 | truth => exact Language.Definable.const True
 | mem i j => exact Language.DefinableRel.comp (P := Membership.mem) (hs j) (hs i)
 | eq i j => exact Language.DefinableRel.comp (P := Eq) (hs i) (hs j)
 | imp A B ia ib => exact (ia s hs).imp (ib s hs)
 | all i A ih =>
   apply Language.Definable.all
   apply ih
   intro j
   by_cases he : j=i
   · subst j
     simpa only [update,if_pos] using
       (Language.DefinableFunction.projection (L := ℒₛₑₜ) (M := V) (k := k+1) 0)
   · change Language.DefinableFunction (L := Language.set) (fun v : Fin (k+1) → V => update (fun j => s j (fun l => v l.succ)) i (v 0) j)
     simp only [update,he,if_neg]
     exact Language.DefinableFunction.substitution (hs j)
       (fun l => Language.DefinableFunction.projection l.succ)

theorem decoded_relation_definable {V : Type*} [SetStructure V]
 (a d h : Nat) (s : Nat → V) :
 ℒₛₑₜ-relation (fun u v => evalCode (fun x y : V => x ∈ y) a (update (update s d u) h v)) := by
 apply named_eval_definable (decodeNat a)
 intro j
 by_cases hjh : j=h
 · subst j
   simpa only [update,if_pos] using
     (Language.DefinableFunction.projection (L := ℒₛₑₜ) (M := V) (k := 2) 1)
 · by_cases hjd : j=d
   · subst j
     simpa [update,hjh] using
       (Language.DefinableFunction.projection (L := ℒₛₑₜ) (M := V) (k := 2) 0)
   · simpa [update,hjh,hjd] using
       (Language.DefinableFunction.const (L := ℒₛₑₜ) (k := 2) (s j))

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun x y : V => x ∈ y)

private lemma update_at {X : Type*} (s : Nat → X) (i j : Nat) (x : X) :
    update s i x j = (if j = i then x else s j) := rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private lemma eval_under_update (a i : Nat) (ha : a ≠ i) (s : Nat → V) (x y : V) :
    evalCode E a (update (update s a x) i y) ↔ evalCode E a (update s i y) := by
  rw [update_commute s a i ha]
  exact evalCode_self_independent a E _ x

/-- The literal pointed gate is valid in every model of ZF. -/
theorem pointedGate_valid (a d h : Nat) (had : a ≠ d) (hah : a ≠ h) (s : Nat → V) :
    evalCode E (pointedGateCode a d h) s := by
  simp only [pointedGateCode, evalCode_imp, evalCode_all, evalCode_mem, evalCode_eq,
    evalCode_one_false E (fun x => mem_irrefl x)]
  let R := fun u v => evalCode E a (update (update s d u) h v)
  obtain ⟨C, hstart, hclosed⟩ := ScottHulls.binary_pointed_hull R
    (decoded_relation_definable a d h s) (s d) (s h)
  have hpoint : evalCode E a s → s h ∈ C := fun hs =>
    hstart (by simpa only [R, update_restore] using hs)
  by_cases hdh : d = h
  · subst d
    simp only [update_same, update_at, hah, Ne.symm hah, ite_false, ite_true,
      eval_under_update a h hah, evalCode_self_independent, forall_const, imp_self]
    intro fail
    apply fail C _ hpoint
    intro z hz noPredecessor
    obtain ⟨p, hp⟩ := (hclosed z hz).1
    have hz' : evalCode E a (update s h z) := by simpa only [R, update_same] using hp
    apply noPredecessor z hz'
    intro _ _ noMember
    exact noMember z hz' hz
  · simp only [update_same, update_shadow, update_at, had, hah, Ne.symm had, Ne.symm hah, hdh,
      Ne.symm hdh, ite_false, ite_true,
      evalCode_erase_self_under_two a h d hah had,
      evalCode_erase_self_under_two a d h had hah,
      update_commute s h d (Ne.symm hdh), evalCode_self_independent,
      forall_const, imp_self]
    intro fail
    apply fail C _ hpoint
    intro z hz noPredecessor
    obtain ⟨⟨p, hp⟩, hcover⟩ := hclosed z hz
    apply noPredecessor p hp
    intro u hu v hv noMember
    obtain ⟨w, hw, hwR⟩ := hcover u hu ⟨v, hv⟩
    exact noMember w hwR hw

end ZFR.FoundationBridge
