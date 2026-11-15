module
public import HeadTwoTemplate
@[expose] public section
namespace ZFR
open C209Soundness

theorem instantiate_shadowed (d : Nat) (p : C209Soundness.Formula) :
    subst (d+1) (translate (bindName d (bindName d id)) p) =
      shift (translate id p) := by
  rw [subst_translate_bind]
  unfold shift
  rw [rename_translate]
  congr 1
  funext j
  by_cases he : j = d
  · subst j; simp [replaceName, bindName]
  · simp [replaceName, bindName,he]

theorem nd_head6_from_irreflexivity {Γ : Context}
    (irr : ∀ i, ND (.seq Γ (.imp (.mem i i) .bot))) (d h : Nat) :
    ND (.seq Γ (translateCode id
      (4*cantor (4*cantor (4*cantor (4*cantor (4*cantor h d+2) 1) d+2) 1) h))) := by
  let H := translateCode id h
  let B := translateCode id (4*cantor (4*cantor (4*cantor h d+2) 1) d+2)
  have hc : 4*cantor (4*cantor h d+2) 1 ≠ 0 := by
    have := cantor_ge_right (4*cantor h d+2) 1; omega
  have hb : 4*cantor (4*cantor (4*cantor (4*cantor h d+2) 1) d+2) 1 ≠ 0 := by
    have := cantor_ge_right (4*cantor (4*cantor (4*cantor h d+2) 1) d+2) 1; omega
  apply nd_imp_code_intro
  rw [translateCode_imp_pos _ _ _ hb, translateCode_one]
  change ND (.seq (.imp B (.mem 0 0)::Γ) H)
  apply ND.ie (ND.pc _ H .bot)
  apply ND.ii
  apply ND.exp
  have hp : ND (.seq (.imp H .bot :: .imp B (.mem 0 0)::Γ) B) := by
    dsimp [B]
    rw [translateCode_all, translateCode_imp_pos _ _ _ hc, translateCode_all]
    apply ND.allI
    apply ND.ii
    have ha : ND (.seq
        ((translateCode (bindName d (bindName d id)) h).all ::
          shiftContext (.imp H .bot :: .imp B (.mem 0 0)::Γ))
        (.all (translateCode (bindName d (bindName d id)) h))) := ND.ctx (by simp)
    have hi := ND.allE (d+1) ha
    change ND (.seq _ (subst (d+1) (translate (bindName d (bindName d id)) (decodeNat h)))) at hi
    rw [instantiate_shadowed] at hi
    apply ND.exp
    apply ND.ie (a := shift H)
    · apply ND.ctx
      simp [shiftContext,shift,rename]
    · simpa only [B, translateCode_all, translateCode_imp_pos _ _ _ hc] using (show ND (.seq _ (shift H)) from hi)
  have hf : ND (.seq (.imp H .bot :: .imp B (.mem 0 0)::Γ) (.mem 0 0)) :=
    ND.ie (ND.ctx (by simp)) hp
  exact ND.ie (irr 0).weaken_cons.weaken_cons hf

end ZFR
