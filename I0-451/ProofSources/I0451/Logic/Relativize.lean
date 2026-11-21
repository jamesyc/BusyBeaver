module
public import I0451.Identity
public import Mathlib.Data.Fin.Tuple.Basic

/-! Relativize formulas to the members of a parameter. An elementary
self-map that fixes that parameter restricts to an elementary self-map
of those members. -/
@[expose] public section
namespace I0451.Identity

variable {D : Type}

def Elementary (E : D → D → Prop) (j : D → D) : Prop :=
  ∀ {n : Nat} (formula : Formula n) (v : Fin n → D),
    formula.eval E v ↔ formula.eval E (j ∘ v)

theorem Elementary.mem_iff {E : D → D → Prop} {j : D → D}
    (map : Elementary E j) (x y : D) : E x y ↔ E (j x) (j y) := by
  let args : Fin 2 → D := Fin.cases x (fun _ : Fin 1 => y)
  exact map (.mem 0 1 : Formula 2) args

def Formula.restrictTo : {n : Nat} → Formula n → Formula (n + 1)
  | _, .mem i k => .mem i.castSucc k.castSucc
  | _, .eq i k => .eq i.castSucc k.castSucc
  | _, .bot => .bot
  | _, .imp a b => .imp a.restrictTo b.restrictTo
  | n, .ex body => .ex ((Formula.mem 0 (Fin.last (n + 1))).conjunction body.restrictTo)

private theorem cases_snoc {n : Nat} (first last : D) (v : Fin n → D) :
    Fin.cases (motive := fun _ => D) first (Fin.snoc v last) =
      Fin.snoc (Fin.cases (motive := fun _ => D) first v) last := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl, Fin.cases_succ, Fin.snoc_last]
    change last = Fin.snoc (α := fun _ => D) (Fin.cases (motive := fun _ => D) first v) last (Fin.last (n + 1))
    simp only [Fin.snoc_last]
  | cast i =>
    rw [Fin.snoc_castSucc]
    cases i using Fin.cases with
    | zero => rfl
    | succ i => simp [Fin.cases_succ, show i.succ.castSucc = i.castSucc.succ from rfl]

theorem Formula.eval_restrictTo (E : D → D → Prop) (bound : D) {n : Nat} (f : Formula n)
    (val : Fin n → {x : D // E x bound}) :
    f.restrictTo.eval E (Fin.snoc (fun i => (val i).val) bound) ↔
      f.eval (fun x y : {x : D // E x bound} => E x.val y.val) val := by
  induction f with
  | mem i k => simp [restrictTo, eval]
  | eq i k => simp [restrictTo, eval, Subtype.ext_iff]
  | bot => rfl
  | imp a b ha hb => simp [restrictTo, eval, ha, hb]
  | ex body ih =>
    simp only [restrictTo, eval, eval_conjunction]
    have values (x : D) (member : E x bound) :
        Fin.cases (motive := fun _ => D) x (Fin.snoc (fun i => (val i).val) bound) =
          Fin.snoc (fun i => (Fin.cases (motive := fun _ => {x : D // E x bound}) ⟨x, member⟩ val i).val) bound := by
      rw [cases_snoc]
      congr 1
      funext i
      cases i using Fin.cases <;> rfl
    have test (x : D) :
        E (Fin.cases x (Fin.snoc (fun i => (val i).val) bound) 0)
          (Fin.cases x (Fin.snoc (fun i => (val i).val) bound) (Fin.last (_ + 1))) ↔ E x bound := by
      rw [cases_snoc]
      simp
    constructor
    · rintro ⟨x, guard, evalBody⟩
      have member := (test x).mp guard
      rw [values x member] at evalBody
      exact ⟨⟨x, member⟩, (ih _).mp evalBody⟩
    · rintro ⟨⟨x, member⟩, evalBody⟩
      refine ⟨x, (test x).mpr member, ?_⟩
      rw [values x member]
      exact (ih _).mpr evalBody

def restrictedMap {E : D → D → Prop} {j : D → D} (preserves : Elementary E j)
    {bound : D} (fixed : j bound = bound) : {x : D // E x bound} → {x : D // E x bound} :=
  fun x => ⟨j x.val, by
    have member := (preserves.mem_iff x.val bound).mp x.property
    exact (congrArg (E (j x.val)) fixed).mp member⟩

theorem Elementary.restricted {E : D → D → Prop} {j : D → D}
    (map : Elementary E j) {bound : D} (fixed : j bound = bound) :
    Elementary (fun x y : {x : D // E x bound} => E x.val y.val) (restrictedMap map fixed) := by
  intro n formula v
  have parameters :
      j ∘ Fin.snoc (fun i => (v i).val) bound =
        Fin.snoc (fun i => ((restrictedMap map fixed ∘ v) i).val) bound := by
    funext i
    induction i using Fin.lastCases with
    | last => simpa [Function.comp_def] using fixed
    | cast i => simp [restrictedMap]
  rw [← formula.eval_restrictTo E bound v, ← formula.eval_restrictTo E bound (restrictedMap map fixed ∘ v),
    ← parameters]
  exact map _ _

theorem Formula.eval_equiv {D' : Type} (q : D ≃ D') (E : D → D → Prop) (E' : D' → D' → Prop)
    (membership : ∀ a b, E a b ↔ E' (q a) (q b)) {n : Nat} (formula : Formula n) (v : Fin n → D) :
    formula.eval E v ↔ formula.eval E' (q ∘ v) := by
  induction formula with
  | mem i j => exact membership _ _
  | eq i j => exact q.injective.eq_iff.symm
  | bot => rfl
  | imp p r hp hr => simp only [eval, hp v, hr v]
  | ex body induction =>
    simp only [eval]
    have assignments (x : D) : q ∘ Fin.cases x v = Fin.cases (q x) (q ∘ v) := by
      funext k
      cases k using Fin.cases <;> rfl
    constructor
    · rintro ⟨x, witnesses⟩
      refine ⟨q x, ?_⟩
      rw [← assignments x]
      exact (induction _).mp witnesses
    · rintro ⟨w, witnesses⟩
      let x := q.symm w
      have exactX : q x = w := q.apply_symm_apply w
      refine ⟨x, (induction _).mpr ?_⟩
      rw [assignments x, exactX]
      exact witnesses

theorem Elementary.transport {D' : Type} {E : D → D → Prop} {E' : D' → D' → Prop}
    {j : D → D} {j' : D' → D'} (elementary : Elementary E j) (q : D ≃ D')
    (membership : ∀ a b, E a b ↔ E' (q a) (q b)) (commute : ∀ x, q (j x) = j' (q x)) :
    Elementary E' j' := by
  intro n formula vals
  let old := q.symm ∘ vals
  have params : q ∘ old = vals := by
    funext i
    exact q.apply_symm_apply (vals i)
  have mapped : q ∘ (j ∘ old) = j' ∘ vals := by
    funext i
    change q (j (q.symm (vals i))) = j' (vals i)
    rw [commute, q.apply_symm_apply]
  have original := formula.eval_equiv q E E' membership old
  have images := formula.eval_equiv q E E' membership (j ∘ old)
  rw [params] at original
  rw [mapped] at images
  exact original.symm.trans ((elementary formula old).trans images)

end I0451.Identity
