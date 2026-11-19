module
public import RankHullParameterSpecialization
public import RankHullEqualLabel
@[expose] public section
namespace ZFR

def bumpPredicate (phi : Formula) := rename (lift Nat.succ) phi

theorem bumpPredicate_comm (phi : Formula) :
 rename (lift (lift Nat.succ)) (bumpPredicate phi) = bumpPredicate (bumpPredicate phi) := by
 simp only [bumpPredicate, rename_comp]
 congr 1
 funext i; cases i <;> rfl

theorem bumpPredicate_subst (phi : Formula) :
 subst 0 (bumpPredicate phi) = phi := by
 simp only [subst, bumpPredicate, rename_comp]
 have he : substMap 0 ∘ lift Nat.succ = id := by funext j; cases j <;> rfl
 rw [he, rename_id]

theorem shift_separationFormula (phi : Formula) :
 shift (separationFormula (rename sepIndex phi)) =
 separationFormula (rename sepIndex (bumpPredicate phi)) := by
 have he : lift (lift (lift Nat.succ)) ∘ sepIndex = sepIndex ∘ lift Nat.succ := by
   funext i; cases i <;> simp [lift,sepIndex,Function.comp_def]
 simp [shift,separationFormula,sourceIff,rename,bumpPredicate,rename_comp,he,lift]

theorem nd_parameterized_separation {Γ : Context} (phi : Formula)
 (hsep : ND (.seq Γ (separationFormula (rename sepIndex phi)))) (s : Nat) :
 ND (.seq Γ (.ex (separatedSpec (s+1) 0 (bumpPredicate phi)))) := by
 have h := ND.allE s hsep
 have he : lift (lift (substMap s)) ∘ sepIndex = lift Nat.succ := by
   funext i; cases i <;> simp [lift,sepIndex,substMap,Function.comp_def, Nat.add_assoc]
 simpa only [separationFormula, sourceIff, separatedSpec, subst, rename,
   rename_comp, he, bumpPredicate, lift, substMap] using h

theorem shift_separatedSpec_general (s b : Nat) (phi : Formula) :
 shift (separatedSpec s b phi) = separatedSpec (s+1) (b+1) (bumpPredicate phi) := by
 simp [shift,separatedSpec,sourceIff,rename,lift,bumpPredicate,Nat.add_assoc]

def parameterizedPointedBody (i : Nat) (phi : Formula) := Formula.and
 (.all (.imp (.mem 0 1) (bumpPredicate phi)))
 (.imp (subst (i+1) (bumpPredicate phi)) (.mem (i+1) 0))

theorem shift_parameterizedPointedEx (i : Nat) (phi : Formula) :
 shift (.ex (parameterizedPointedBody i phi)) =
 .ex (parameterizedPointedBody (i+1) (bumpPredicate phi)) := by
 simp only [shift,parameterizedPointedBody,rename,rename_subst,bumpPredicate_comm]
 simp [lift,Nat.add_assoc]

theorem subst_parameterizedPointedBody (i : Nat) (phi : Formula) :
 subst 0 (parameterizedPointedBody i phi) =
 .and (.all (.imp (.mem 0 1) phi)) (.imp (subst i phi) (.mem i 0)) := by
 have he : rename (lift (substMap 0)) (bumpPredicate phi) = phi := by
   simp only [bumpPredicate, rename_comp]
   have hm : lift (substMap 0) ∘ lift Nat.succ = id := by
     funext j; cases j <;> rfl
   rw [hm, rename_id]
 change rename (substMap 0) (parameterizedPointedBody i phi) = _
 simp only [parameterizedPointedBody,rename,rename_subst,he]
 simp [lift,substMap]

theorem nd_parameterized_singleton {Γ : Context} (n : Nat) (phi : Formula)
 (hphi : Bound phi (n+1)) (hr : zfrRefl ∈ Γ) (hp : zfrPair ∈ Γ)
 (hs : separationSchema n phi ∈ Γ) (i : Nat) :
 ND (.seq Γ (.ex (parameterizedPointedBody i phi))) := by
 have hsep := nd_separation_declose n phi hphi hs
 have hpair := nd_pair_singleton hp i
 apply ND.exE hpair
 let Δ := singletonSpec (i+1) 0 :: shiftContext Γ
 have hr' : zfrRefl ∈ Δ := List.mem_cons_of_mem _ (shifted_member hr shift_zfrRefl)
 have hsg : ND (.seq Δ (singletonSpec (i+1) 0)) := ND.ctx (by simp [Δ])
 have his : ND (.seq Δ (.mem (i+1) 0)) := ND.ie
   (ND.ce2 (nd_singleton_instance hsg (i+1))) (ND.di1 (nd_refl_instance hr' (i+1)))
 have hsep' : ND (.seq Δ (separationFormula (rename sepIndex (bumpPredicate phi)))) := by
   have hh := nd_weaken_head (b := singletonSpec (i+1) 0) (nd_shift hsep)
   simpa only [shift_separationFormula] using hh
 have hse := nd_parameterized_separation (bumpPredicate phi) hsep' 0
 apply ND.exE hse
 let P := bumpPredicate (bumpPredicate phi)
 let Θ := separatedSpec 1 0 P :: shiftContext Δ
 have hspec : ND (.seq Θ (separatedSpec 1 0 P)) := ND.ctx (by simp [Θ])
 have his' : ND (.seq Θ (.mem (i+2) 1)) := by
   simpa [Θ, shift, rename, Nat.add_assoc] using nd_weaken_head (b := separatedSpec 1 0 P) (nd_shift his)
 have hgood : ND (.seq Θ (.all (.imp (.mem 0 1) P))) := by
   apply ND.allI
   apply ND.ii
   have ht : ND (.seq (.mem 0 1 :: shiftContext Θ) (separatedSpec 2 1 (bumpPredicate P))) := by
     have hh := nd_weaken_head (b := .mem 0 1) (nd_shift hspec)
     simpa only [shift_separatedSpec_general] using hh
   have hh := nd_separated_instance 2 1 (bumpPredicate P) ht 0
   have hh' := ND.ce2 (ND.ie (ND.ce1 hh) (ND.ctx (by simp)))
   simpa only [bumpPredicate_subst] using hh'
 have hpoint : ND (.seq Θ (.imp (subst (i+2) P) (.mem (i+2) 0))) := by
   apply ND.ii
   have hh := nd_weaken_head (b := subst (i+2) P)
     (ND.ce2 (nd_separated_instance 1 0 P hspec (i+2)))
   exact ND.ie hh (ND.ci (nd_weaken_head his') (ND.ctx (by simp)))
 have hout : ND (.seq Θ (.ex (parameterizedPointedBody (i+2) P))) := by
   apply ND.exI 0
   rw [subst_parameterizedPointedBody]
   exact ND.ci hgood hpoint
 simpa only [shift_parameterizedPointedEx, Nat.add_assoc] using hout

def parameterizedSeparationContext (n : Nat) (phi : Formula) : Context :=
 [zfrRefl,zfrPair,separationSchema n phi]

theorem parameterizedSeparationContext_closed (n : Nat) (phi : Formula) (hphi : Bound phi (n+1)) :
 ClosedContext (parameterizedSeparationContext n phi) := by
 intro a ha
 simp only [parameterizedSeparationContext,List.mem_cons,List.not_mem_nil,or_false] at ha
 rcases ha with rfl | rfl | rfl
 · simp [zfrRefl, Bound]
 · simp [zfrPair, Bound]
 · exact separationSchema_closed n phi hphi

theorem parameterized_singleton_certificate (n : Nat) (phi : Formula) (hphi : Bound phi (n+1)) (i : Nat) :
 ClosedSeparation (separationSchema n phi) ∧
 ClosedContext (parameterizedSeparationContext n phi) ∧
 ND (.seq (parameterizedSeparationContext n phi) (.ex (parameterizedPointedBody i phi))) := by
 refine ⟨separationSchema_recognized n phi hphi,parameterizedSeparationContext_closed n phi hphi,?_⟩
 exact nd_parameterized_singleton n phi hphi
   (by simp [parameterizedSeparationContext]) (by simp [parameterizedSeparationContext])
   (by simp [parameterizedSeparationContext]) i

end ZFR
