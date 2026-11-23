module
public import I3_334.Proof.GuardedAlgebra
@[expose] public section

namespace PalomarI3334

open PalomarI3380 (RawTerm RawContext)
open Templates

/-- The ground search may instantiate the ten equations and rewrite either
side in any context. The guard is imposed on the actual closed substitution. -/
inductive Derives : RawTerm → RawTerm → Prop where
  | refl (t : RawTerm) : Derives t t
  | symm {s t : RawTerm} : Derives s t → Derives t s
  | trans {r s t : RawTerm} : Derives r s → Derives s t → Derives r t
  | instanceOf {eq : Equation} (listed : eq ∈ equations) (values : Fin 4 → RawTerm)
      (safe : Guarded (values 3)) : Derives (eq.1.instantiate values) (eq.2.instantiate values)
  | context (ctx : RawContext) {s t : RawTerm} : Derives s t → Derives (ctx.fill s) (ctx.fill t)

theorem Derives.sound {A : Type} {M : NativeAlgebra A} (model : M.Models) {s t : RawTerm}
    (h : Derives s t) : M.evalRaw s = M.evalRaw t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ i₁ i₂ => exact i₁.trans i₂
  | instanceOf listed _ safe => exact model.ground listed _ safe
  | context ctx _ ih =>
    induction ctx with
    | hole => exact ih
    | app tag before nested after ihCtx =>
      simp only [RawContext.fill, NativeAlgebra.evalRaw, RawTerm.fold_app, List.map_append,
        List.map_cons, NativeAlgebra.evalRaw] at ihCtx ⊢
      rw [ihCtx]

namespace Derives

def setoid : Setoid RawTerm where
  r := Derives
  iseqv := ⟨refl, symm, trans⟩

abbrev Classes := Quotient setoid

def classOf (t : RawTerm) : Classes := Quotient.mk setoid t

theorem class_eq_iff {s t : RawTerm} : classOf s = classOf t ↔ Derives s t :=
  ⟨fun eq => Quotient.exact (s := setoid) eq, fun rel => Quotient.sound (s := setoid) rel⟩

structure Application (tag : Nat) where
  run : List RawTerm → Classes
  congr {left right : List RawTerm} :
    (∀ rest, Derives (.app tag (left ++ rest)) (.app tag (right ++ rest))) → run left = run right

def application (tag : Nat) : List Classes → Application tag
  | [] => ⟨fun before => classOf (.app tag before), fun related =>
    class_eq_iff.mpr (by simpa only [List.append_nil] using related [])⟩
  | value :: values =>
    let tail := application tag values
    let extend (before : List RawTerm) :=
      Quotient.liftOn value (fun t => tail.run (before ++ [t])) fun s t related =>
        tail.congr fun rest => by
          simpa only [RawContext.fill, List.append_assoc, List.singleton_append] using
            (context (.app tag before .hole rest) related)
    ⟨extend, by
      intro left right related
      induction value using Quotient.inductionOn with
      | _ representative =>
        change tail.run (left ++ [representative]) = tail.run (right ++ [representative])
        apply tail.congr
        intro rest
        simpa only [List.append_assoc] using related ([representative] ++ rest)⟩

def applyApp (tag : Nat) (args : List Classes) (before : List RawTerm) : Classes :=
  (application tag args).run before

theorem applyApp_map (tag : Nat) (children before : List RawTerm) :
    applyApp tag (children.map classOf) before = classOf (.app tag (before ++ children)) := by
  induction children generalizing before with
  | nil => simp only [applyApp, application, List.map_nil, List.append_nil]
  | cons i rest ih =>
    change applyApp tag (rest.map classOf) (before ++ [i]) = _
    simpa only [List.append_assoc, List.singleton_append] using ih (before ++ [i])

def termAlgebra : NativeAlgebra Classes where
  domain := classOf (.app 1 [])
  embedding := classOf (.app 0 [])
  membership := classOf (.app 2 [])
  seed := classOf (.app 3 [])
  identity := classOf (.app 5 [])
  neg x := applyApp 3 [x] []
  converse x := applyApp 4 [x] []
  choice x := applyApp 1 [x] []
  nand x y := applyApp 3 [x, y] []
  product x y := applyApp 4 [x, y] []
  other tag args := applyApp tag args []

theorem operation_termAlgebra (tag : Nat) (args : List Classes) :
    termAlgebra.operation tag args = applyApp tag args [] := by
  unfold NativeAlgebra.operation
  split <;> rfl

theorem evalRaw_termAlgebra (t : RawTerm) : termAlgebra.evalRaw t = classOf t := by
  obtain ⟨tag, children⟩ := t
  simp only [NativeAlgebra.evalRaw, RawTerm.fold_app, operation_termAlgebra]
  have same : List.map (RawTerm.fold termAlgebra.operation) children = children.map classOf := by
    apply List.map_congr_left
    intro child mem
    exact evalRaw_termAlgebra child
  rw [same, applyApp_map, List.nil_append]
termination_by sizeOf t
decreasing_by have h := List.sizeOf_lt_of_mem mem; simp_wf; omega

theorem models_termAlgebra : termAlgebra.Models := by
  apply NativeAlgebra.models_of_raw
  intro eq listed a b c d safe
  induction a using Quotient.inductionOn with | _ a =>
  induction b using Quotient.inductionOn with | _ b =>
  induction c using Quotient.inductionOn with | _ c =>
  let values := NativeAlgebra.valuation a b c d
  have safe' : Guarded (values 3) := safe
  have valuation_eval : termAlgebra.evalRaw ∘ values =
      NativeAlgebra.valuation (classOf a) (classOf b) (classOf c) (termAlgebra.evalRaw d) := by
    funext i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> simp [values, NativeAlgebra.valuation,
      evalRaw_termAlgebra] <;> rfl
  have inst : termAlgebra.evalRaw (eq.1.instantiate values) =
      termAlgebra.evalRaw (eq.2.instantiate values) := by
    simpa only [evalRaw_termAlgebra] using class_eq_iff.mpr (instanceOf listed values safe')
  simpa only [NativeAlgebra.eval_instantiate, valuation_eval, classOf] using inst

end Derives

/-- Equational completeness for the guarded syntax, before any interpretation
as membership relations. -/
theorem guarded_derives_iff (s t : RawTerm) :
    Derives s t ↔ ∀ (A : Type) (M : NativeAlgebra A), M.Models → M.evalRaw s = M.evalRaw t := by
  refine ⟨fun h _ _ model => h.sound model, fun h => Derives.class_eq_iff.mp ?_⟩
  simpa only [Derives.evalRaw_termAlgebra] using
    h _ Derives.termAlgebra Derives.models_termAlgebra

end PalomarI3334
