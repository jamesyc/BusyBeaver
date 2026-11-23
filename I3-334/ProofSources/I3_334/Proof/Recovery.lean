module
public import I3_334.Proof.Ground
public import I3_334.Proof.ModelEquations
public import I3_334Support.Equations.RecoveredI3
@[expose] public section

namespace PalomarI3334.NativeAlgebra

open PalomarI3380 Templates

variable {A : Type} (M : NativeAlgebra A)

private theorem guarded_app {tag : Nat} {children : List RawTerm} (tagOk : 3 ≤ tag)
    (all : ∀ t ∈ children, Guarded t) : Guarded (.app tag children) := by
  intro token member
  simp only [RawTerm.tokens_app, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨t, mem, ht⟩
  · exact tagOk
  · exact all t mem token ht

theorem SafeValue.constructor {x y z : A}
    (hx : M.SafeValue x) (hy : M.SafeValue y) (hz : M.SafeValue z) :
    M.SafeValue (M.meet (M.product x (M.converse y)) (M.nand y z)) := by
  rcases hx with ⟨tx, sx, ex⟩
  rcases hy with ⟨ty, sy, ey⟩
  rcases hz with ⟨tz, sz, ez⟩
  have conv : Guarded (.app 4 [ty]) :=
    guarded_app (by decide) (by simpa using sy)
  have prod : Guarded (.app 4 [tx, .app 4 [ty]]) :=
    guarded_app (by decide) (by simpa using And.intro sx conv)
  have nand : Guarded (.app 3 [ty, tz]) :=
    guarded_app (by decide) (by simpa using And.intro sy sz)
  have pair : Guarded (.app 3 [.app 4 [tx, .app 4 [ty]], .app 3 [ty, tz]]) :=
    guarded_app (by decide) (by simpa using And.intro prod nand)
  refine ⟨.app 3 [.app 3 [.app 4 [tx, .app 4 [ty]], .app 3 [ty, tz]]],
    guarded_app (by decide) (by simpa using pair), ?_⟩
  simp only [evalRaw_app, List.map_cons, List.map_nil, NativeAlgebra.operation]
  change M.neg (M.nand (M.product (M.evalRaw tx) (M.converse (M.evalRaw ty)))
      (M.nand (M.evalRaw ty) (M.evalRaw tz))) = _
  rw [ex, ey, ez]
  rfl

variable (safe : A → Prop)

/-- The second coordinate reserves a code for the seed while still
allowing every guarded value to serve as a code. -/
noncomputable def decodeLocal (code : A × Bool) : A := by
  classical
  exact if code.2 then M.seed else if safe code.1 then code.1 else M.seed

theorem decodeLocal_safe (code : A × Bool) (seed : safe M.seed) : safe (M.decodeLocal safe code) := by
  classical
  unfold decodeLocal
  split
  · exact seed
  · split
    · assumption
    · exact seed

theorem decodeLocal_code {x : A} (guard : safe x) : M.decodeLocal safe (x, false) = x := by
  classical
  simp [decodeLocal, guard]

/-- The two-element relation algebra on a singleton with empty membership
and embedding. It realizes the same finite equations. -/
def selectorAlgebra : Algebra Bool where
  constant
    | .D | .J | .E => false
    | _ => true
  neg := not
  converse := id
  choice := id
  localRel _ := false
  nand x y := !(x && y)
  product := Bool.and
  node _ _ _ := false

noncomputable def legacy : Algebra (A × Bool) where
  constant c := ((M.relationAlgebra id (fun a _ _ => a)).constant c, selectorAlgebra.constant c)
  neg x := (M.neg x.1, !x.2)
  converse x := (M.converse x.1, x.2)
  choice x := (M.maskedChoice x.1, x.2)
  localRel x := (M.decodeLocal safe x, false)
  nand x y := (M.nand x.1 y.1, !(x.2 && y.2))
  product x y := (M.product x.1 y.1, x.2 && y.2)
  node x y z :=
    let p := M.product (M.decodeLocal safe x) (M.converse (M.decodeLocal safe y))
    let n := M.nand (M.decodeLocal safe y) (M.decodeLocal safe z)
    (M.meet p n, false)

theorem legacy_eval_bit {V : Type} (v : V → A × Bool) (t : Term V) :
    ((M.legacy safe).eval v t).2 = selectorAlgebra.eval (Prod.snd ∘ v) t := by
  induction t <;> simp only [Algebra.eval, legacy, selectorAlgebra, Function.comp_apply, id] at * <;> simp only [*]

theorem selector_models : selectorAlgebra.Models Manifest.preceding := by
  intro eq listed v
  have cases : v = (fun i => if i.val = 0 then v 0 else if i.val = 1 then v 1 else v 2) := by
    funext i
    have indexes : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases indexes with rfl | rfl | rfl <;> rfl
  generalize val0 : v 0 = x at cases
  generalize val1 : v 1 = y at cases
  generalize val2 : v 2 = z at cases
  rw [cases]
  simp only [Manifest.preceding, Manifest.retained, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h <;> subst eq <;> cases x <;> cases y <;> cases z <;> rfl

theorem legacy_ambient (model : M.ModelsOn safe) : (M.legacy safe).Models ambientEquations := by
  intro eq listed v
  have fst := model.ambient id (fun a _ _ => a) eq listed (Prod.fst ∘ v)
  apply Prod.ext
  · simp only [ambientEquations, Manifest.preceding, Manifest.retained, List.cons_append,
      List.nil_append, List.take_succ_cons, List.take_zero, List.mem_cons,
      List.not_mem_nil, or_false] at listed
    rcases listed with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst eq <;> exact fst
  · rw [M.legacy_eval_bit safe, M.legacy_eval_bit safe]
    exact selector_models eq (List.mem_of_mem_take listed) _

theorem legacy_models (model : M.ModelsOn safe)
    (closed : ∀ {x y z : A}, safe x → safe y → safe z →
      safe (M.meet (M.product x (M.converse y)) (M.nand y z))) : (M.legacy safe).Models Manifest.preceding := by
  intro eq listed v
  by_cases ambient : eq ∈ ambientEquations
  · exact M.legacy_ambient safe model eq ambient v
  apply Prod.ext
  case snd =>
    rw [M.legacy_eval_bit safe, M.legacy_eval_bit safe]
    exact selector_models eq listed _
  have split : Manifest.preceding = ambientEquations ++ [
      (.localRel (.const .I), .product (.const .E) (.const .D)),
      (.localRel (.node Manifest.a Manifest.b Manifest.c),
        Manifest.meet (.product (.localRel Manifest.a) (.converse (.localRel Manifest.b)))
          (.nand (.localRel Manifest.b) (.localRel Manifest.c))),
      (Manifest.meet (.product (.product (.converse (.const .J)) (.localRel Manifest.a)) (.const .J))
        (.neg (.localRel Manifest.a)), .neg (.const .U))] := rfl
  rw [split, List.mem_append] at listed
  have localRows := listed.resolve_left ambient
  simp only [List.mem_cons, List.not_mem_nil, or_false] at localRows
  rcases localRows with rfl | rfl | rfl
  · exact model.seed
  · exact M.decodeLocal_code safe
      (closed (M.decodeLocal_safe safe _ model.seed_safe)
        (M.decodeLocal_safe safe _ model.seed_safe) (M.decodeLocal_safe safe _ model.seed_safe))
  · let l := M.decodeLocal safe (v 0)
    have guard := M.decodeLocal_safe safe (v 0) model.seed_safe
    change M.meet (M.product (M.product (M.converse M.embedding) l) M.embedding)
      (M.neg l) = M.bottomValue
    rw [← model.associative (M.converse M.embedding)]
    exact (model.boolean.disjoint_iff_le M.membership _ _).mpr (model.guarded_preservation l guard)

end PalomarI3334.NativeAlgebra

namespace PalomarI3334

open PalomarI3380

theorem consistency_of_guarded_underivability (h : ¬ Derives (.app 1 []) (.app 0 [])) :
    Logic.ZFCI3Consistent := by
  apply PalomarI3380.consistency_of_equational_underivability
  intro derives
  let M := Derives.termAlgebra
  let legacy := M.legacy M.SafeValue
  have model := M.legacy_models M.SafeValue Derives.models_termAlgebra (NativeAlgebra.SafeValue.constructor M)
  have old := legacy.models_final_of_preceding model
  have equality := PalomarI3380.Derives.sound legacy old derives
  have same : Derives.classOf (.app 1 []) = Derives.classOf (.app 0 []) :=
    congrArg Prod.fst equality
  exact h (Derives.class_eq_iff.mp same)

end PalomarI3334
