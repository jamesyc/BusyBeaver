module
public import ZF192Support.Logic.Source.Derived.Equivalence
@[expose] public section
namespace ZFR

theorem nd_not_all_not_to_exists (Γ : Context) (p : Formula) :
 ND (.seq Γ (.imp (.imp (.all (.imp p .bot)) .bot) (.ex p))) := by
 apply ND.ii
 apply ND.ie (ND.pc _ (.ex p) .bot)
 apply ND.ii
 apply ND.exp
 apply ND.ie (a := .all (.imp p .bot)) (ND.ctx (by simp))
 apply ND.allI
 apply ND.ii
 have hp : ND (.seq (p :: shiftContext
     (.imp (.ex p) .bot :: .imp (.all (.imp p .bot)) .bot :: Γ)) p) := ND.ctx (by simp)
 have he : ND (.seq (p :: shiftContext
     (.imp (.ex p) .bot :: .imp (.all (.imp p .bot)) .bot :: Γ))
     (.ex (rename (lift Nat.succ) p))) := by
   apply ND.exI 0
   rw [subst_lift_shift]
   exact hp
 apply ND.ie (a := .ex (rename (lift Nat.succ) p)) (b := .bot)
 · apply ND.ctx; simp [shiftContext,shift,rename]
 · exact he

theorem nd_exists_to_not_all_not (Γ : Context) (p : Formula) :
 ND (.seq Γ (.imp (.ex p) (.imp (.all (.imp p .bot)) .bot))) := by
 apply ND.ii
 apply ND.ii
 apply ND.exE (a := p)
 · exact ND.ctx (by simp)
 · have hu : ND (.seq (p :: shiftContext (.all (.imp p .bot) :: .ex p :: Γ))
       (.all (rename (lift Nat.succ) (.imp p .bot)))) := by
     apply ND.ctx; simp [shiftContext,shift,rename]
   have hi := ND.allE 0 hu
   rw [subst_lift_shift] at hi
   exact ND.ie hi (ND.ctx (by simp))

theorem NDEquiv.ex_encoding (Γ : Context) (p : Formula) :
 NDEquiv Γ (.ex p) (.imp (.all (.imp p .bot)) .bot) :=
 ⟨nd_exists_to_not_all_not Γ p,nd_not_all_not_to_exists Γ p⟩

theorem NDEquiv.curry (Γ : Context) (p q r : Formula) :
 NDEquiv Γ (.imp (.and p q) r) (.imp p (.imp q r)) := by
 constructor
 · apply ND.ii; apply ND.ii; apply ND.ii
   apply ND.ie (a := .and p q) (ND.ctx (by simp))
   exact ND.ci (ND.ctx (by simp)) (ND.ctx (by simp))
 · apply ND.ii; apply ND.ii
   have hpq : ND (.seq (.and p q :: .imp p (.imp q r) :: Γ) (.and p q)) := ND.ctx (by simp)
   exact ND.ie (ND.ie (ND.ctx (by simp)) (ND.ce1 hpq)) (ND.ce2 hpq)

theorem NDEquiv.ex_and_encoding (Γ : Context) (p q : Formula) :
 NDEquiv Γ (.ex (.and p q)) (.imp (.all (.imp p (.imp q .bot))) .bot) :=
 (NDEquiv.ex_encoding Γ (.and p q)).trans
   ((NDEquiv.all (NDEquiv.curry (shiftContext Γ) p q .bot)).imp (NDEquiv.refl Γ .bot))

end ZFR
