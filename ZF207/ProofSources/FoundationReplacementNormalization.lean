module
public import FoundationReplacementSyntax
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
theorem rep_nested (p : SetTheorySemiproposition 2) :
 Rewriting.subst (Rewriting.subst p ![(.bvar 1 : Semiterm Language.set Nat 2),.bvar 0])
   ((.bvar 0 : Semiterm Language.set Nat 3) :> (fun _ : Fin 1 => .bvar 2)) =
 Rewriting.subst p ![(.bvar 2 : Semiterm Language.set Nat 3),.bvar 0] := by
 unfold Rewriting.subst
 rw [← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
 congr 2
 apply congrArg Rew.subst
 funext i
 refine Fin.cases ?_ (fun j => ?_) i
 · rfl
 · have hj : j=0 := Fin.eq_zero j; subst j; rfl

theorem repTotal_equiv (p : SetTheorySemiproposition 2) (Γ : Context) :
 NDEquiv Γ (toSource (repTotal p)) (totalUnique (toSource p)) := by
 apply NDEquiv.all
 apply NDEquiv.ex
 apply NDEquiv.and
 · have hi : (#0 :> fun x => #(BinderNotation.finSuccItr x 1) : Fin 2 → Semiterm Language.set Nat 2) = Semiterm.bvar := by
     funext i
     refine Fin.cases rfl (fun j => ?_) i
     have hj : j=0 := Fin.eq_zero j
     subst j; rfl
   simp only [hi,Rewriting.subst,Rew.subst_eq_id,ReflectiveRewriting.id_app]
   rw [rep_subst_swap]; exact NDEquiv.refl _ _
 · apply NDEquiv.all
   have hh := toSource_arrow_equiv (shiftContext (shiftContext (shiftContext Γ)))
     (Rewriting.subst p ![(.bvar 2 : Semiterm Language.set Nat 3),.bvar 0])
     (.rel .eq ![.bvar 0,.bvar 1])
   convert hh using 1 <;> simp [toSource,atom,termIndex,rep_subst_B]
   exact ⟨congrArg (fun q => toSource (Semiformula.neg q)) (rep_nested p),rfl⟩


def repRangeSource (phi : Formula) : Formula :=
 .all (.ex (.all (sourceIff (.mem 0 1) (.ex (.and (.mem 0 3) (rename repCIndex phi))))))

theorem repRange_equiv (p : SetTheorySemiproposition 2) (Γ : Context) :
 NDEquiv Γ (toSource (repRange p)) (repRangeSource (toSource p)) := by
 apply NDEquiv.all; apply NDEquiv.ex; apply NDEquiv.all
 have hh := toSource_iff_equiv (shiftContext (shiftContext (shiftContext Γ)))
   (.rel .mem ![.bvar 0,.bvar 1] : Semiformula Language.set Nat 3)
   (.exs (.and (.rel .mem ![.bvar 0,.bvar 3])
     (Rewriting.subst p ![(.bvar 0 : Semiterm Language.set Nat 4),.bvar 1])))
 convert hh using 1 <;> simp [toSource,atom,termIndex,rep_subst_C,sourceIff]
 all_goals
   refine ⟨⟨rfl,?_⟩,rfl,rfl⟩
   change toSource (Semiformula.exs (.and (.rel .mem ![.bvar 0,.bvar 3]) (Rewriting.subst p ![(.bvar 0 : Semiterm Language.set Nat 4),.bvar 1]))) = _
   simp only [toSource,atom,Matrix.cons_val_zero,Matrix.cons_val_one,termIndex]
   congr 2
   exact rep_subst_C p

theorem repOpen_equiv (p : SetTheorySemiproposition 2) (Γ : Context) :
 NDEquiv Γ (toSource (repOpen p)) (.imp (totalUnique (toSource p)) (repRangeSource (toSource p))) :=
 (toSource_arrow_equiv Γ (repTotal p) (repRange p)).trans
   ((repTotal_equiv p Γ).imp (repRange_equiv p Γ))


end ZFR.FoundationBridge
