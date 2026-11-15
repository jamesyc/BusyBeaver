module
public import SourceSyntax
@[expose] public section
namespace ZFR
abbrev Context := List Formula

def ContextSub (Γ Δ : Context) : Prop := ∀ a, a ∈ Γ → a ∈ Δ
inductive Row where
 | seq : Context → Formula → Row
 | branches : Context → Formula → Formula → Formula → Row
 deriving DecidableEq, Repr

def renameContext (σ : Nat → Nat) (Γ : Context) := Γ.map (rename σ)
def shiftContext (Γ : Context) := Γ.map shift
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

inductive ND : Row → Prop where
 | ctx {Γ a} : a ∈ Γ → ND (.seq Γ a)
 | pc (Γ a b) : ND (.seq Γ (.imp (.imp (.imp a b) a) a))
 | ii {Γ a b} : ND (.seq (a :: Γ) b) → ND (.seq Γ (.imp a b))
 | ie {Γ a b} : ND (.seq Γ (.imp a b)) → ND (.seq Γ a) → ND (.seq Γ b)
 | exp {Γ a} : ND (.seq Γ .bot) → ND (.seq Γ a)
 | ci {Γ a b} : ND (.seq Γ a) → ND (.seq Γ b) → ND (.seq Γ (.and a b))
 | ce1 {Γ a b} : ND (.seq Γ (.and a b)) → ND (.seq Γ a)
 | ce2 {Γ a b} : ND (.seq Γ (.and a b)) → ND (.seq Γ b)
 | di1 {Γ a b} : ND (.seq Γ a) → ND (.seq Γ (.or a b))
 | di2 {Γ a b} : ND (.seq Γ b) → ND (.seq Γ (.or a b))
 | branchPair {Γ a b c} : ND (.seq (a :: Γ) c) → ND (.seq (b :: Γ) c) → ND (.branches Γ a b c)
 | de {Γ a b c} : ND (.seq Γ (.or a b)) → ND (.branches Γ a b c) → ND (.seq Γ c)
 | wk {Γ Δ a} : ContextSub Γ Δ → ND (.seq Γ a) → ND (.seq Δ a)
 | allI {Γ a} : ND (.seq (shiftContext Γ) a) → ND (.seq Γ (.all a))
 | allE {Γ a} (t : Nat) : ND (.seq Γ (.all a)) → ND (.seq Γ (subst t a))
 | exI {Γ a} (t : Nat) : ND (.seq Γ (subst t a)) → ND (.seq Γ (.ex a))
 | exE {Γ a c} : ND (.seq Γ (.ex a)) → ND (.seq (a :: shiftContext Γ) (shift c)) → ND (.seq Γ c)

theorem ND.rename {r : Row} (h : ND r) (σ : Nat → Nat) : ND (renameRow σ r) := by
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

end ZFR
