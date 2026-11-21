module
public import I3_380.Search.Compiler.Source
public import I3_380.RelationAlgebra.Laws
public import I3_380.Ground
@[expose] public section

namespace PalomarI3380.Compiler.Source

open Manifest Term

private theorem layout_exact : (rowLayout.map Prod.fst).Perm final := by
  decide +kernel

private theorem layout_sound {A : Type} (M : Algebra A)
    (basis₁ : M.Satisfies meredith1) (basis₂ : M.Satisfies meredith2)
    (assoc : M.Satisfies productAssociative) :
    ∀ r ∈ rowLayout, M.Satisfies r.1 ↔ M.Satisfies r.2 := by
  have symm (e : Equation) : M.Satisfies e ↔ M.Satisfies (swapEquation e) :=
    ⟨fun h v => (h v).symm, fun h v => (h v).symm⟩
  have mul (x y z : A) : M.product (M.product x y) z = M.product x (M.product y z) :=
    (assoc (fun i => if i.val = 0 then x else if i.val = 1 then y else z)).symm
  have boolean := meredithLaws M.inf M.neg
    (fun x y => basis₁ (fun i => if i.val = 0 then x else y))
    (fun x y z => basis₂ (fun i => if i.val = 0 then x else if i.val = 1 then y else z))
  have commute (x y : A) : M.inf x y = M.inf y x := boolean.commutative x y
  intro row mem
  simp only [rowLayout, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq <;>
    subst row
  · exact symm (reduce converseMeet)
  · rfl
  · change (∀ v : Fin 3 → A,
      M.nand (M.product (M.product (M.converse (M.constant .J)) (M.localRel (v 0))) (M.constant .J))
        (M.neg (M.localRel (v 0))) = M.constant .U) ↔
      (∀ v : Fin 3 → A,
      M.nand (M.product (M.converse (M.constant .J)) (M.product (M.localRel (v 1)) (M.constant .J)))
        (M.neg (M.localRel (v 1))) = M.constant .U)
    simp only [mul]
    exact ⟨fun h v => h (fun _ => v 1), fun h v => h (fun _ => v 0)⟩
  · change (∀ v : Fin 3 → A, M.converse (M.converse (v 0)) = v 0) ↔
      (∀ v : Fin 3 → A, v 1 = M.converse (M.converse (v 1)))
    exact ⟨fun h v => (h (fun _ => v 1)).symm, fun h v => (h (fun _ => v 0)).symm⟩
  · exact symm (reduce choiceDomain)
  · rfl
  · let e := M.constant .E
    let t := M.neg (M.product (M.converse e) (M.neg e))
    let s := M.product (M.converse (M.choice t)) (M.choice t)
    let base := M.product s (M.converse e)
    change (∀ _ : Fin 3 → A, base = M.product (M.product base s) (M.converse t)) ↔
      (∀ _ : Fin 3 → A, M.product base (M.product s (M.converse t)) = base)
    rw [mul]
    exact ⟨fun h v => (h v).symm, fun h v => (h v).symm⟩
  · exact symm meredith1
  · let t := M.neg (M.product (M.converse (M.constant .E)) (M.neg (M.constant .E)))
    change (∀ _ : Fin 3 → A, M.inf t (M.converse t) = M.constant .I) ↔
      (∀ _ : Fin 3 → A, M.inf (M.converse t) t = M.constant .I)
    rw [commute t (M.converse t)]
  · rfl
  · exact symm final[17]
  · rfl
  · rfl
  · let e := M.constant .E
    let u := M.constant .U
    let pre := fun v : Fin 3 → A => M.product (M.converse e) (M.choice (v 0))
    let p := fun v => M.neg (M.product (pre v) (M.neg e))
    let q := fun v => M.neg (M.product (M.neg (pre v)) e)
    let pp := fun v : Fin 3 → A => M.neg (M.product (M.converse e) (M.product (M.choice (v 0)) (M.neg e)))
    change (∀ v : Fin 3 → A, M.product (M.inf (p v) (q v)) u = u) ↔
      (∀ v : Fin 3 → A, M.product (M.inf (q v) (pp v)) u = u)
    have reshape (v : Fin 3 → A) : p v = pp v := by dsimp only [p, pp, pre]; rw [mul]
    apply forall_congr'
    intro v
    rw [reshape v, commute (pp v) (q v)]
  · exact symm (reduce defineDomain)
  · rfl
  · exact symm meredith2
  · let t := M.neg (M.product (M.converse (M.constant .E)) (M.neg (M.constant .E)))
    let s := M.product (M.converse (M.choice t)) (M.choice t)
    let act := fun r => M.inf (M.constant .I)
      (M.product (M.product (M.constant .E) r) (M.constant .U))
    change (∀ _ : Fin 3 → A, M.constant .D = act (M.inf s (M.constant .D))) ↔
      (∀ _ : Fin 3 → A, act (M.inf (M.constant .D) s) = M.constant .D)
    rw [commute s (M.constant .D)]
    exact ⟨fun h v => (h v).symm, fun h v => (h v).symm⟩
  · rfl

/-- The executed trie presents the same theory as the conservative basis,
including the rows reassociated by the archive. -/
theorem source_models_iff {A : Type} (M : Algebra A) :
    M.Models rows ↔ M.Models final := by
  have transfer (h₁ : M.Satisfies meredith1) (h₂ : M.Satisfies meredith2)
      (assoc : M.Satisfies productAssociative) :
      M.Models rows ↔ M.Models final := by
    constructor
    · intro h e he
      obtain ⟨r, hr, same⟩ := List.mem_map.mp ((layout_exact.mem_iff).mpr he)
      have actual := h r.2 (List.mem_map.mpr ⟨r, hr, rfl⟩)
      exact same ▸ (layout_sound M h₁ h₂ assoc r hr).mpr actual
    · intro h e he
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
      exact (layout_sound M h₁ h₂ assoc r hr).mp
        (h r.1 (layout_exact.mem_iff.mp (List.mem_map.mpr ⟨r, hr, rfl⟩)))
  constructor
  · intro h
    have m₁ := h (swapEquation meredith1) (by simp [rows, rowLayout])
    have m₂ := h (swapEquation meredith2) (by simp [rows, rowLayout])
    have a := h productAssociative (by decide +kernel)
    exact (transfer (fun v => (m₁ v).symm) (fun v => (m₂ v).symm) a).mp h
  · intro h
    have m₁ := h meredith1 (by simp [final])
    have m₂ := h meredith2 (by simp [final])
    have a := h productAssociative (layout_exact.mem_iff.mp (by decide +kernel))
    exact (transfer m₁ m₂ a).mpr h

theorem source_derives_iff {a b : ClosedTerm} : Derives rows a b ↔ Derives final a b := by
  constructor
  · intro h
    apply Derives.complete
    intro A M hM
    exact h.sound M ((source_models_iff M).mpr hM)
  · intro h
    apply Derives.complete
    intro A M hM
    exact h.sound M ((source_models_iff M).mp hM)

end PalomarI3380.Compiler.Source
