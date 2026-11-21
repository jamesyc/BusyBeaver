module
public import I0451.Logic.TruthOperations

/-! Equality of two coordinates is generated from membership by
extensionality on the transitive domain. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode
open I0451.Logic.ZFModel (common_nat_bound avoid_nat_label)

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

theorem atomicSet_eval_decode {d g : V} {f : Domain E d → Domain E d}
    (decoded : Encodes E d g f) (inside : g ∈ assignments d) (x y : Domain E d) :
    g ∈ atomicSet (assignments d) x.val y.val ↔ (f x).val ∈ (f y).val := by
  rw [mem_atomicSet, and_iff_right inside]
  constructor
  · intro trace
    exact trace _ _ ((decoded.at_iff x _).mpr rfl) ((decoded.at_iff y _).mpr rfl)
  · intro value a b atA atB
    rw [← (decoded.at_iff x a).mp atA, ← (decoded.at_iff y b).mp atB]
    exact value

theorem generated_equality {d : V} (transitive : IsTransitive d) (omega : (ω : V) ⊆ d)
    (x y : Domain E d) :
    ∃ R ∈ generated d (assignments d), ∀ g (f : Domain E d → Domain E d),
      Encodes E d g f → (g ∈ R ↔ f x = f y) := by
  classical
  let U := assignments d
  let ops := ZFModel.setOperations (V := V)
  obtain ⟨m, hm, avoidsX⟩ := avoid_nat_label x.val
  obtain ⟨n, hn, avoidsY⟩ := avoid_nat_label y.val
  obtain ⟨label, hlabel, bx, by_⟩ := common_nat_bound m n hm hn
  let k : Domain E d := ⟨label, omega label hlabel⟩
  have dx : x ≠ k := fun eq => avoidsX label hlabel (fun h => mem_irrefl label (bx label h))
    (congrArg Subtype.val eq)
  have dy : y ≠ k := fun eq => avoidsY label hlabel (fun h => mem_irrefl label (by_ label h))
    (congrArg Subtype.val eq)
  have left := (generated_closed d U).atom k.val x.val k.property x.property
  have right := (generated_closed d U).atom k.val y.val k.property y.property
  obtain ⟨comparison, inComparison, checks⟩ := generated_biconditional omega left right
  obtain ⟨R, inR, universally⟩ := generated_universal omega k.property inComparison
  refine ⟨R, inR, fun g f decoded => ?_⟩
  have inside : g ∈ U := (mem_universe d _).mpr ((is_map_iff_encodes ops).mpr ⟨_, decoded⟩)
  rw [universally g inside]
  constructor
  · intro holds
    apply Subtype.ext
    apply mem_ext_iff.mpr
    intro z
    by_cases zD : z ∈ d
    · obtain ⟨h, codeH, changed⟩ := decoded.replace ops k ⟨z, zD⟩
      have hU : h ∈ U := (mem_universe _ _).mpr ((is_map_iff_encodes ops).mpr ⟨_, codeH⟩)
      have same := SameExcept.of_agree k.property inside hU changed
      have test := (checks h hU).mp (holds h hU same)
      rw [atomicSet_eval_decode codeH hU, atomicSet_eval_decode codeH hU] at test
      simpa [Identity.replace, dx, dy] using test
    · have noX : z ∉ (f x).val := fun mem => zD (transitive.transitive _ (f x).property z mem)
      have noY : z ∉ (f y).val := fun mem => zD (transitive.transitive _ (f y).property z mem)
      simp [noX, noY]
  · intro eq h hU same
    obtain ⟨p, codeH⟩ := (is_map_iff_encodes ops).mp ((mem_universe _ _).mp hU)
    have sameX := decoded_eq decoded codeH same x (fun eq => dx (Subtype.ext eq))
    have sameY := decoded_eq decoded codeH same y (fun eq => dy (Subtype.ext eq))
    apply (checks h hU).mpr
    rw [atomicSet_eval_decode codeH hU, atomicSet_eval_decode codeH hU, ← sameX, ← sameY, eq]

end I0451.Logic.SetAssignments
