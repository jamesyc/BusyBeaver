module
public import FoundationClosureBridge
public import FoundationSourceEncoding
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder

theorem termIndex_bound {n m : Nat} (t : Semiterm Language.set Nat n)
 (h : ∀ j, t.FVar? j → j<m) : termIndex t < n+m := by
 cases t with
 | bvar i => simp only [termIndex]; omega
 | fvar j => have hj := h j (by simp); simp only [termIndex]; omega
 | func f v => exact Empty.elim f

theorem toSource_bound {n m : Nat} (p : Semiformula Language.set Nat n)
 (h : ∀ j, p.FVar? j → j<m) : Bound (toSource p) (n+m) := by
 induction p using Semiformula.rec' with
 | hverum => exact ⟨trivial,trivial⟩
 | hfalsum => trivial
 | hrel r v =>
   have hv (i : Fin _) := termIndex_bound (v i) (fun j hj => h j (by simp; exact ⟨i,hj⟩))
   cases r <;> exact ⟨hv 0,hv 1⟩
 | hnrel r v =>
   have hv (i : Fin _) := termIndex_bound (v i) (fun j hj => h j (by simp; exact ⟨i,hj⟩))
   cases r <;> exact ⟨⟨hv 0,hv 1⟩,trivial⟩
 | hand p q ihp ihq =>
   exact ⟨ihp (fun j hj => h j (by simp [hj])),ihq (fun j hj => h j (by simp [hj]))⟩
 | hor p q ihp ihq =>
   exact ⟨ihp (fun j hj => h j (by simp [hj])),ihq (fun j hj => h j (by simp [hj]))⟩
 | hall p ih =>
   have hp := ih (fun j hj => h j (by simpa using hj))
   simpa [toSource,Bound,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp
 | hexs p ih =>
   have hp := ih (fun j hj => h j (by simpa using hj))
   simpa [toSource,Bound,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp

theorem toSource_bound_fvSup (p : Proposition Language.set) : Bound (toSource p) p.fvSup := by
 simpa using toSource_bound p (fun _ hj => Semiformula.lt_fvSup_of_fvar? hj)

theorem foundation_source_declose (p : Proposition Language.set)
 (h : SourceTheorem (toSource (p.univCl : Proposition Language.set))) :
 SourceTheorem (toSource p) := by
 obtain ⟨Γ,hΓ,hp⟩ := h
 rw [toSource_univCl] at hp
 exact ⟨Γ,hΓ,nd_declose p.fvSup (toSource p) (toSource_bound_fvSup p) hp⟩

end ZFR.FoundationBridge
