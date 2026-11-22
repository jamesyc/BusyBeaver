module
public import ZF192Support.Logic.Source.Syntax
@[expose] public section
namespace ZFR
export PalomarZF192Theory (Context ContextSub Row shiftContext ND)

namespace Row
export PalomarZF192Theory.Row (seq branches)
end Row

namespace ND
export PalomarZF192Theory.ND (ctx pc ii ie exp ci ce1 ce2 di1 di2 branchPair de wk allI allE exI exE)
end ND

def renameContext (σ : Nat → Nat) (Γ : Context) := Γ.map (rename σ)
def renameRow (σ : Nat → Nat) : Row → Row
 | .seq Γ a => .seq (renameContext σ Γ) (rename σ a)
 | .branches Γ a b c => .branches (renameContext σ Γ) (rename σ a) (rename σ b) (rename σ c)

theorem renameContext_shift (σ : Nat → Nat) (Γ : Context) :
 renameContext (lift σ) (shiftContext Γ) = shiftContext (renameContext σ Γ) := by
 simp only [renameContext, shiftContext, List.map_map]
 apply List.map_congr_left
 intro a _; exact rename_shift σ a

theorem contextSub_rename (σ : Nat → Nat) {Γ Δ : Context} (h : ContextSub Γ Δ) :
 ContextSub (renameContext σ Γ) (renameContext σ Δ) := by
 intro a ha
 obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
 exact List.mem_map.mpr ⟨b, h b hb, rfl⟩

theorem _root_.PalomarZF192Theory.ND.rename {r : Row} (h : ND r) (σ : Nat → Nat) : ND (renameRow σ r) := by
 induction h generalizing σ with
 | ctx hm => exact ND.ctx (List.mem_map.mpr ⟨_, hm, rfl⟩)
 | pc Γ a b => exact ND.pc _ _ _
 | ii h ih => exact ND.ii (ih σ)
 | ie h1 h2 ih1 ih2 => exact ND.ie (ih1 σ) (ih2 σ)
 | exp h ih => exact ND.exp (ih σ)
 | ci h1 h2 ih1 ih2 => exact ND.ci (ih1 σ) (ih2 σ)
 | ce1 h ih => exact ND.ce1 (ih σ)
 | ce2 h ih => exact ND.ce2 (ih σ)
 | di1 h ih => exact ND.di1 (ih σ)
 | di2 h ih => exact ND.di2 (ih σ)
 | branchPair h1 h2 ih1 ih2 => exact ND.branchPair (ih1 σ) (ih2 σ)
 | de h1 h2 ih1 ih2 => exact ND.de (ih1 σ) (ih2 σ)
 | wk hs h ih => exact ND.wk (contextSub_rename σ hs) (ih σ)
 | allI h ih =>
   apply ND.allI
   have hx := ih (lift σ)
   simpa only [renameRow, renameContext_shift] using hx
 | allE t h ih =>
   have hx := ND.allE (σ t) (ih σ)
   simpa only [renameRow, rename, rename_subst] using hx
 | exI t h ih =>
   apply ND.exI (σ t)
   have hx := ih σ
   simpa only [renameRow, rename_subst] using hx
 | exE h1 h2 ih1 ih2 =>
   apply ND.exE (ih1 σ)
   have hx := ih2 (lift σ)
   change ND (.seq (ZFR.rename (lift σ) _ :: renameContext (lift σ) (shiftContext _)) (ZFR.rename (lift σ) (shift _))) at hx
   simpa only [renameContext_shift, rename_shift] using hx

theorem _root_.PalomarZF192Theory.ND.weaken_cons {Γ : Context} {p q : Formula} (h : ND (.seq Γ p)) :
    ND (.seq (q::Γ) p) := ND.wk (fun _ ha => List.mem_cons_of_mem _ ha) h

theorem nd_truth (Γ : Context) : ND (.seq Γ (.imp .bot .bot)) :=
  ND.ii (ND.ctx (by simp))

end ZFR
