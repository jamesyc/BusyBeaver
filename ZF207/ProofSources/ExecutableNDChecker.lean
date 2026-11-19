module
public import SourceND
@[expose] public section
namespace ZFR.Executable

/-- Untyped finite certificate data, containing no Lean proof fields. -/
inductive Cert where
 | ctx (Γ : Context) (a : Formula)
 | pc (Γ : Context) (a b : Formula)
 | ii (Γ : Context) (a b : Formula) (p : Cert)
 | ie (Γ : Context) (a b : Formula) (p q : Cert)
 | exp (Γ : Context) (a : Formula) (p : Cert)
 | ci (Γ : Context) (a b : Formula) (p q : Cert)
 | ce1 (Γ : Context) (a b : Formula) (p : Cert)
 | ce2 (Γ : Context) (a b : Formula) (p : Cert)
 | di1 (Γ : Context) (a b : Formula) (p : Cert)
 | di2 (Γ : Context) (a b : Formula) (p : Cert)
 | branchPair (Γ : Context) (a b c : Formula) (p q : Cert)
 | de (Γ : Context) (a b c : Formula) (p q : Cert)
 | wk (Γ Δ : Context) (a : Formula) (p : Cert)
 | allI (Γ : Context) (a : Formula) (p : Cert)
 | allE (Γ : Context) (a : Formula) (t : Nat) (p : Cert)
 | exI (Γ : Context) (a : Formula) (t : Nat) (p : Cert)
 | exE (Γ : Context) (a c : Formula) (p q : Cert)
 deriving Repr

abbrev Checked := { r : Row // ND r }

/-- Checked equality of the actual conclusion to the premise required by a rule.
All logical fields are erased during execution; this is a computable checker. -/
def demand (actual : Option Checked) (expected : Row) : Option (PLift (ND expected)) := do
 let ⟨r, hr⟩ ← actual
 if h : r = expected then pure ⟨h ▸ hr⟩ else none

def check : Cert → Option Checked
 | .ctx Γ a => if h : a ∈ Γ then some ⟨.seq Γ a, ND.ctx h⟩ else none
 | .pc Γ a b => some ⟨_, ND.pc Γ a b⟩
 | .ii Γ a b p => do
   let hp ← demand (check p) (.seq (a :: Γ) b)
   pure ⟨_, ND.ii hp.down⟩
 | .ie Γ a b p q => do
   let hp ← demand (check p) (.seq Γ (.imp a b))
   let hq ← demand (check q) (.seq Γ a)
   pure ⟨_, ND.ie hp.down hq.down⟩
 | .exp Γ a p => do
   let hp ← demand (check p) (.seq Γ .bot)
   pure ⟨.seq Γ a, ND.exp hp.down⟩
 | .ci Γ a b p q => do
   let hp ← demand (check p) (.seq Γ a)
   let hq ← demand (check q) (.seq Γ b)
   pure ⟨_, ND.ci hp.down hq.down⟩
 | .ce1 Γ a b p => do
   let hp ← demand (check p) (.seq Γ (.and a b))
   pure ⟨_, ND.ce1 hp.down⟩
 | .ce2 Γ a b p => do
   let hp ← demand (check p) (.seq Γ (.and a b))
   pure ⟨_, ND.ce2 hp.down⟩
 | .di1 Γ a b p => do
   let hp ← demand (check p) (.seq Γ a)
   pure ⟨.seq Γ (.or a b), ND.di1 hp.down⟩
 | .di2 Γ a b p => do
   let hp ← demand (check p) (.seq Γ b)
   pure ⟨.seq Γ (.or a b), ND.di2 hp.down⟩
 | .branchPair Γ a b c p q => do
   let hp ← demand (check p) (.seq (a :: Γ) c)
   let hq ← demand (check q) (.seq (b :: Γ) c)
   pure ⟨_, ND.branchPair hp.down hq.down⟩
 | .de Γ a b c p q => do
   let hp ← demand (check p) (.seq Γ (.or a b))
   let hq ← demand (check q) (.branches Γ a b c)
   pure ⟨_, ND.de hp.down hq.down⟩
 | .wk Γ Δ a p => do
   let hp ← demand (check p) (.seq Γ a)
   if h : ∀ x ∈ Γ, x ∈ Δ then
     pure ⟨_, ND.wk h hp.down⟩
   else none
 | .allI Γ a p => do
   let hp ← demand (check p) (.seq (shiftContext Γ) a)
   pure ⟨_, ND.allI hp.down⟩
 | .allE Γ a t p => do
   let hp ← demand (check p) (.seq Γ (.all a))
   pure ⟨_, ND.allE t hp.down⟩
 | .exI Γ a t p => do
   let hp ← demand (check p) (.seq Γ (subst t a))
   pure ⟨_, ND.exI t hp.down⟩
 | .exE Γ a c p q => do
   let hp ← demand (check p) (.seq Γ (.ex a))
   let hq ← demand (check q) (.seq (a :: shiftContext Γ) (shift c))
   pure ⟨_, ND.exE hp.down hq.down⟩

/-- Actual executable output. No Classical.propDecidable or noncomputable code. -/
def conclusion (certificate : Cert) : Option Row := (check certificate).map Subtype.val

theorem sound (certificate : Cert) (row : Row)
    (accepted : conclusion certificate = some row) : ND row := by
 unfold conclusion at accepted
 cases h : check certificate with
 | none => simp [h] at accepted
 | some result =>
   have eq : result.val = row := by simpa [h] using accepted
   exact eq ▸ result.property

/-- Every exact source-ND derivation has an accepted finite certificate.
This is completeness of the executable inference checker, not ZF-axiom recognition. -/
theorem complete_checked {row : Row} (h : ND row) :
    ∃ certificate, check certificate = some ⟨row, h⟩ := by
 induction h with
 | @ctx Γ a hm => exact ⟨.ctx Γ a, by simp [check, hm]⟩
 | pc Γ a b => exact ⟨.pc Γ a b, rfl⟩
 | @ii Γ a b h ih =>
   obtain ⟨p, hp⟩ := ih
   exact ⟨.ii Γ a b p, by simp [check, demand, hp]⟩
 | @exp Γ a h ih =>
   obtain ⟨p, hp⟩ := ih
   exact ⟨.exp Γ a p, by simp [check, demand, hp]⟩
 | @ce1 Γ a b h ih =>
   obtain ⟨p, hp⟩ := ih
   exact ⟨.ce1 Γ a b p, by simp [check, demand, hp]⟩
 | @ce2 Γ a b h ih =>
   obtain ⟨p, hp⟩ := ih
   exact ⟨.ce2 Γ a b p, by simp [check, demand, hp]⟩
 | @di1 Γ a b h ih =>
   obtain ⟨p, hp⟩ := ih
   exact ⟨.di1 Γ a b p, by simp [check, demand, hp]⟩
 | @di2 Γ a b h ih =>
   obtain ⟨p, hp⟩ := ih
   exact ⟨.di2 Γ a b p, by simp [check, demand, hp]⟩
 | @allI Γ a h ih =>
   obtain ⟨p, hp⟩ := ih
   exact ⟨.allI Γ a p, by simp [check, demand, hp]⟩
 | @ie Γ a b h1 h2 ih1 ih2 =>
   obtain ⟨p, hp⟩ := ih1
   obtain ⟨q, hq⟩ := ih2
   exact ⟨.ie Γ a b p q, by simp [check, demand, hp, hq]⟩
 | @ci Γ a b h1 h2 ih1 ih2 =>
   obtain ⟨p, hp⟩ := ih1
   obtain ⟨q, hq⟩ := ih2
   exact ⟨.ci Γ a b p q, by simp [check, demand, hp, hq]⟩
 | @branchPair Γ a b c h1 h2 ih1 ih2 =>
   obtain ⟨p, hp⟩ := ih1
   obtain ⟨q, hq⟩ := ih2
   exact ⟨.branchPair Γ a b c p q, by simp [check, demand, hp, hq]⟩
 | @de Γ a b c h1 h2 ih1 ih2 =>
   obtain ⟨p, hp⟩ := ih1
   obtain ⟨q, hq⟩ := ih2
   exact ⟨.de Γ a b c p q, by simp [check, demand, hp, hq]⟩
 | @exE Γ a c h1 h2 ih1 ih2 =>
   obtain ⟨p, hp⟩ := ih1
   obtain ⟨q, hq⟩ := ih2
   exact ⟨.exE Γ a c p q, by simp [check, demand, hp, hq]⟩
 | @wk Γ Δ a hs h ih =>
   obtain ⟨p, hp⟩ := ih
   exact ⟨.wk Γ Δ a p, by simp [check, demand, hp]; exact hs⟩
 | @allE Γ a t h ih =>
   obtain ⟨p, hp⟩ := ih
   exact ⟨.allE Γ a t p, by simp [check, demand, hp]⟩
 | @exI Γ a t h ih =>
   obtain ⟨p, hp⟩ := ih
   exact ⟨.exI Γ a t p, by simp [check, demand, hp]⟩

theorem complete {row : Row} (h : ND row) : ∃ certificate, conclusion certificate = some row := by
 obtain ⟨certificate, hc⟩ := complete_checked h
 exact ⟨certificate, by simp [conclusion, hc]⟩


end ZFR.Executable
