module
public import DirectFramedRows
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Basic
@[expose] public section
namespace RosserDirect.FramedRowEquality
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Control where
 | tag | contextEntry (branches : Bool) | contextBody (branches : Bool)
 | formula (remaining : Fin 3) | equal | different
 deriving DecidableEq, Fintype, Inhabited

def active : Control → Prop
 | .equal | .different => False
 | _ => True
instance (q : Control) : Decidable (active q) := by cases q <;> unfold active <;> infer_instance

def finish (n : Fin 3) : Control :=
 if h : n.val = 0 then .equal else .formula ⟨n.val-1, by omega⟩

def advance : Control → Symbol → Control
 | .tag, .bit0 => .contextEntry false
 | .tag, .bit1 => .contextEntry true
 | .tag, _ => .different
 | .contextEntry b, .frameEnd => .formula (if b then 2 else 0)
 | .contextEntry b, _ => .contextBody b
 | .contextBody b, .frameEnd => .contextEntry b
 | .contextBody b, _ => .contextBody b
 | .formula n, .frameEnd => finish n
 | .formula n, _ => .formula n
 | q, _ => q

/-- Recognizer paths stop exactly at the row boundary. Active-state premises
exclude premature acceptance, which is needed for prefix-free comparison. -/
inductive Path : Control → List Symbol → Control → Prop where
 | nil (q) : Path q [] q
 | cons {q x xs r} : active q → Path (advance q x) xs r → Path q (x :: xs) r

theorem Path.append {q r s : Control} {xs ys : List Symbol}
    (h : Path q xs r) (g : Path r ys s) : Path q (xs ++ ys) s := by
 induction h with
 | nil => exact g
 | cons ha h ih => exact .cons ha (ih g)

def machine (q : Control) : Stmt Control :=
 if active q then
 .pop .input (fun _ x => x)
  (.pop .output (fun x y => if x == y then x else none)
    (.branch Option.isSome (.goto (fun x => advance q (x.getD .bit0)))
      (.goto (fun _ => .different))))
 else .halt

theorem same_step (q : Control) (ha : active q) (x : Symbol)
    (v : Option Symbol) (a scratch b : List Symbol) :
 TM2.step machine (config q v (x :: a) scratch (x :: b)) =
 some (config (advance q x) (some x) a scratch b) := by
 cases x <;> simp [machine, ha, config, storage, TM2.step, TM2.stepAux, Function.update]
 all_goals funext k; cases k <;> rfl

theorem different_step (q : Control) (ha : active q) (x y : Symbol) (hne : x ≠ y)
    (v : Option Symbol) (a scratch b : List Symbol) :
 TM2.step machine (config q v (x :: a) scratch (y :: b)) =
 some (config .different none a scratch b) := by
 cases x <;> cases y <;> simp_all [machine, config, storage, TM2.step, TM2.stepAux, Function.update]
 all_goals funext k; cases k <;> rfl

theorem compare_paths {q : Control} {p : List Symbol} (hp : Path q p .equal)
    (s : List Symbol) (hs : Path q s .equal)
    (v : Option Symbol) (a scratch b : List Symbol) :
 ∃ w left right, TM2.Reaches machine
   (config q v (p ++ a) scratch (s ++ b))
   (config (if p = s then .equal else .different) w left scratch right) := by
 induction p generalizing q s v with
 | nil =>
   cases hp
   cases hs with
   | nil => exact ⟨v,a,b,Relation.ReflTransGen.refl⟩
   | cons ha => exact False.elim ha
 | cons x xs ih =>
   cases hp with
   | cons ha hp =>
     cases hs with
     | nil => exact False.elim ha
     | @cons _ y ys _ _ hs =>
       by_cases hxy : x = y
       · subst y
         obtain ⟨w,l,r,hr⟩ := ih hp ys hs (some x)
         have one : TM2.Reaches machine
           (config q v ((x :: xs) ++ a) scratch ((x :: ys) ++ b))
           (config (advance q x) (some x) (xs ++ a) scratch (ys ++ b)) :=
           Relation.ReflTransGen.single (by rw [List.cons_append,List.cons_append,same_step q ha]; rfl)
         exact ⟨w,l,r,by simpa [TM2.Reaches] using one.trans hr⟩
       · refine ⟨none, xs ++ a, ys ++ b, Relation.ReflTransGen.single ?_⟩
         simp only [List.cons_append]
         rw [different_step q ha x y hxy]
         simp [hxy]

theorem formula_path (n : Fin 3) (p : List Symbol)
    (valid : ∀ x ∈ p, x ≠ .frameEnd) :
 Path (.formula n) (p ++ [.frameEnd]) (finish n) := by
 induction p with
 | nil => exact .cons trivial (.nil _)
 | cons x xs ih =>
   refine Path.cons (q := .formula n) trivial ?_
   have hx := valid x (by simp)
   have hi := ih (by intro y hy; exact valid y (by simp [hy]))
   cases x <;> simp_all [advance]

theorem body_path (kind : Bool) (p : List Symbol)
    (valid : ∀ x ∈ p, x ≠ .frameEnd) :
 Path (.contextBody kind) (p ++ [.frameEnd]) (.contextEntry kind) := by
 induction p with
 | nil => exact .cons trivial (.nil _)
 | cons x xs ih =>
   refine Path.cons (q := .contextBody kind) trivial ?_
   have hx := valid x (by simp)
   have hi := ih (by intro y hy; exact valid y (by simp [hy]))
   cases x <;> simp_all [advance]

theorem entry_formula_path (kind : Bool) (p : ZFR.Formula) :
 Path (.contextEntry kind) (FramedRow.formulaFrame p) (.contextEntry kind) := by
 obtain ⟨x,xs,hp⟩ := List.exists_cons_of_ne_nil (FramedContext.formula_nonempty p)
 have hv : ∀ y ∈ x :: xs, y ≠ .frameEnd := by rw [← hp]; exact payloadBits_no_end _
 have hx := hv x (by simp)
 have hi := body_path kind xs (by intro y hy; exact hv y (by simp [hy]))
 unfold FramedRow.formulaFrame
 rw [hp,List.cons_append]
 refine Path.cons (q := .contextEntry kind) trivial ?_
 cases x <;> simp_all [advance]

theorem context_path (kind : Bool) (Γ : ZFR.Context) :
 Path (.contextEntry kind) (FramedContext.encode Γ) (.formula (if kind then 2 else 0)) := by
 induction Γ with
 | nil => exact .cons trivial (.nil _)
 | cons p Γ ih =>
   simpa [FramedRow.formulaFrame, FramedContext.encode, Membership.contextFrames,
     Membership.frames, List.append_assoc] using (entry_formula_path kind p).append ih

theorem row_path (r : ZFR.Row) : Path .tag (FramedRow.encode r) .equal := by
 cases r with
 | seq Γ p =>
   refine Path.cons (q := .tag) trivial ?_
   exact (context_path false Γ).append (formula_path 0 _ (payloadBits_no_end _))
 | branches Γ p q r =>
   refine Path.cons (q := .tag) trivial ?_
   have hp := formula_path 2 (Membership.formulaPayload p) (payloadBits_no_end _)
   have hq := formula_path 1 (Membership.formulaPayload q) (payloadBits_no_end _)
   have hr := formula_path 0 (Membership.formulaPayload r) (payloadBits_no_end _)
   exact (((context_path true Γ).append hp).append hq).append hr

/-- Concrete finite machine compares complete revised-ABI rows, including
all context entries and all formula fields; never stops at the first delimiter. -/
theorem compare_rows (r s : ZFR.Row) (v : Option Symbol) (a scratch b : List Symbol) :
 ∃ w left right, TM2.Reaches machine
   (config .tag v (FramedRow.encode r ++ a) scratch (FramedRow.encode s ++ b))
   (config (if r = s then .equal else .different) w left scratch right) := by
 simpa only [FramedRow.exact_row_equality] using
   compare_paths (row_path r) _ (row_path s) v a scratch b

theorem compare_same_path {q r : Control} {p : List Symbol} (hp : Path q p r)
    (v : Option Symbol) (a scratch b : List Symbol) :
 ∃ w, TM2.Reaches machine
   (config q v (p ++ a) scratch (p ++ b)) (config r w a scratch b) := by
 induction hp generalizing v with
 | nil => exact ⟨v,Relation.ReflTransGen.refl⟩
 | @cons q x xs r ha hp ih =>
   obtain ⟨w,hw⟩ := ih (some x)
   have one : TM2.Reaches machine
     (config q v ((x :: xs) ++ a) scratch ((x :: xs) ++ b))
     (config (advance q x) (some x) (xs ++ a) scratch (xs ++ b)) :=
     Relation.ReflTransGen.single (by rw [List.cons_append,List.cons_append,same_step q ha]; rfl)
   exact ⟨w,one.trans hw⟩

/-- On success, exactly one row is consumed on each side. Both trailing row
stacks and the scratch stack survive unchanged. -/
theorem equal_rows_exact (r : ZFR.Row) (v : Option Symbol) (a scratch b : List Symbol) :
 ∃ w, TM2.Reaches machine
   (config .tag v (FramedRow.encode r ++ a) scratch (FramedRow.encode r ++ b))
   (config .equal w a scratch b) := compare_same_path (row_path r) v a scratch b

end RosserDirect.FramedRowEquality
