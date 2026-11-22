module
public import ZF192Support.Logic.Foundation.Syntax.ToSource
@[expose] public section
namespace ZFR.FoundationBridge
open FFL.FirstOrder

theorem termIndex_bShift {n : Nat} (t : Semiterm Language.set Nat n) :
 termIndex (Rew.bShift t) = termIndex t + 1 := by
 cases t with
 | bvar i => rfl
 | fvar j => simp [termIndex]; omega
 | func f v => exact Empty.elim f

def RewAgrees {n m : Nat} (ω : Rew Language.set Nat n Nat m) (σ : Nat → Nat) :=
 ∀ t, termIndex (ω t) = σ (termIndex t)

theorem RewAgrees.q {n m : Nat} {ω : Rew Language.set Nat n Nat m} {σ : Nat → Nat}
 (h : RewAgrees ω σ) : RewAgrees ω.q (ZFR.lift σ) := by
 intro t
 cases t with
 | bvar i =>
   refine Fin.cases ?_ (fun j => ?_) i
   · simp [termIndex,ZFR.lift]
   · rw [Rew.q_bvar_succ,termIndex_bShift,h (.bvar j)]
     rfl
 | fvar j =>
   change termIndex (Rew.bShift (ω (.fvar j))) = ZFR.lift σ (n+1+j)
   rw [termIndex_bShift,h (.fvar j)]
   simp only [termIndex]
   have he : n+1+j = (n+j)+1 := by omega
   rw [he,ZFR.lift_succ]
 | func f v => exact Empty.elim f

theorem toSource_rew {n : Nat} (p : Semiformula Language.set Nat n)
 {m : Nat} (ω : Rew Language.set Nat n Nat m) (σ : Nat → Nat) (h : RewAgrees ω σ) :
 toSource (Semiformula.rewAux ω p) = ZFR.rename σ (toSource p) := by
 induction p using Semiformula.rec' generalizing m σ with
 | hverum => rfl
 | hfalsum => rfl
 | hrel r v =>
   cases r <;> simp [Semiformula.rewAux,toSource,atom,ZFR.rename,h (v 0),h (v 1)]
 | hnrel r v =>
   cases r <;> simp [Semiformula.rewAux,toSource,atom,ZFR.rename,h (v 0),h (v 1)]
 | hand p q ihp ihq => simp only [Semiformula.rewAux,toSource,ZFR.rename,ihp ω σ h,ihq ω σ h]
 | hor p q ihp ihq => simp only [Semiformula.rewAux,toSource,ZFR.rename,ihp ω σ h,ihq ω σ h]
 | hall p ih =>
   simp only [Semiformula.rewAux,toSource,ZFR.rename]
   exact congrArg ZFR.Formula.all (ih ω.q (ZFR.lift σ) h.q)
 | hexs p ih =>
   simp only [Semiformula.rewAux,toSource,ZFR.rename]
   exact congrArg ZFR.Formula.ex (ih ω.q (ZFR.lift σ) h.q)

theorem agrees_shift : RewAgrees (Rew.shift (L := Language.set) (n := 0)) Nat.succ := by
 intro t
 cases t with
 | bvar i => exact Fin.elim0 i
 | fvar j => rfl
 | func f v => exact Empty.elim f

theorem agrees_free : RewAgrees (Rew.free (L := Language.set) (n := 0)) id := by
 intro t
 cases t with
 | bvar i =>
   have hi : i = 0 := Fin.eq_zero i
   subst i
   rfl
 | fvar j =>
   rw [Rew.free_fvar]
   simp [termIndex]
   omega
 | func f v => exact Empty.elim f

theorem agrees_subst (t : Semiterm Language.set Nat 0) :
 RewAgrees (Rew.subst (fun _ : Fin 1 => t)) (ZFR.substMap (termIndex t)) := by
 intro s
 cases s with
 | bvar i =>
   have hi : i = 0 := Fin.eq_zero i
   subst i
   simp [termIndex,ZFR.substMap]
 | fvar j =>
   rw [Rew.subst_fvar]
   simp only [termIndex,Nat.zero_add]
   have he : 1+j = j+1 := by omega
   rw [he]; rfl
 | func f v => exact Empty.elim f

theorem toSource_shift (p : Semiformula Language.set Nat 0) :
 toSource (Semiformula.rewAux Rew.shift p) = ZFR.shift (toSource p) :=
 toSource_rew p Rew.shift Nat.succ agrees_shift

theorem toSource_free (p : Semiformula Language.set Nat 1) :
 toSource (Semiformula.rewAux Rew.free p) = toSource p := by
 rw [toSource_rew p Rew.free id agrees_free,ZFR.rename_id]

theorem toSource_subst (p : Semiformula Language.set Nat 1)
 (t : Semiterm Language.set Nat 0) :
 toSource (Semiformula.rewAux (Rew.subst (fun _ : Fin 1 => t)) p) =
 ZFR.subst (termIndex t) (toSource p) :=
 toSource_rew p _ _ (agrees_subst t)

end ZFR.FoundationBridge
