module
public import EqualityTemplates
public import NamedInstantiation
@[expose] public section
namespace ZFR
open C207Soundness

theorem translateCode_one (ρ : Nat → Nat) : translateCode ρ 1 = .mem (ρ 0) (ρ 0) :=
  translateCode_mem ρ 0 0

theorem ND.weaken_cons {Γ : Context} {p q : Formula} (h : ND (.seq Γ p)) :
    ND (.seq (q::Γ) p) := ND.wk (fun _ ha => List.mem_cons_of_mem _ ha) h

/-- Logical part of exact head2. The irreflexivity premise must be supplied
by a concrete source Foundation derivation, not model soundness. -/
theorem nd_head2_from_irreflexivity {Γ : Context} (hr : zfrRefl ∈ Γ)
    (irr : ∀ i, ND (.seq Γ (.imp (.mem i i) .bot))) (d h : Nat) :
    ND (.seq Γ (translateCode id
      (4*cantor (4*cantor (4*cantor (4*cantor h d+3) 1) d+2) 1))) := by
  apply nd_imp_code_intro
  apply ND.exp
  have hp : 4*cantor (4*cantor h d+3) 1 ≠ 0 := by
    have := cantor_ge_right (4*cantor h d+3) 1; omega
  have ha : ND (.seq (translateCode id (4*cantor (4*cantor (4*cantor h d+3) 1) d+2)::Γ)
      (.all (translateCode (bindName d id) (4*cantor (4*cantor h d+3) 1)))) := by
    rw [← translateCode_all]; exact ND.ctx (by simp)
  have hi := ND.allE h ha
  rw [subst_translateCode_bind, translateCode_imp_pos _ _ _ hp,
    translateCode_eq, translateCode_one] at hi
  have heq : replaceName d h id h = h := by simp [replaceName]
  have hd : replaceName d h id d = h := by simp [replaceName]
  rw [heq, hd] at hi
  exact ND.ie (irr (replaceName d h id 0)).weaken_cons
    (ND.ie hi (nd_refl_instance hr h).weaken_cons)

end ZFR
