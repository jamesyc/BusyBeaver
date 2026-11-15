module
public import QuantifierTemplates
@[expose] public section
namespace ZFR

def swap01 : Nat → Nat
 | 0 => 1
 | 1 => 0
 | n+2 => n+2

theorem commute_substitutions (p : Formula) :
    subst 1 (rename (lift (substMap 0))
      (rename (lift (lift Nat.succ)) (rename (lift (lift Nat.succ)) p))) =
    rename swap01 p := by
  simp only [subst, rename_comp]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

/-- Universal quantifiers commute after the required de Bruijn exchange. -/
theorem nd_all_commute (Γ : Context) (p : Formula) :
    ND (.seq Γ (.imp (.all (.all p)) (.all (.all (rename swap01 p))))) := by
  apply ND.ii
  apply ND.allI
  apply ND.allI
  have hc : ND (.seq (shiftContext (shiftContext (.all (.all p)::Γ)))
    (.all (.all (rename (lift (lift Nat.succ)) (rename (lift (lift Nat.succ)) p))))) := by
    apply ND.ctx
    simp [shiftContext, shift, rename]
  have hs := ND.allE 1 (ND.allE 0 hc)
  simp only [subst, rename] at hs
  change ND (.seq _ (subst 1 (rename (lift (substMap 0))
    (rename (lift (lift Nat.succ)) (rename (lift (lift Nat.succ)) p))))) at hs
  rw [commute_substitutions] at hs
  exact hs

end ZFR
