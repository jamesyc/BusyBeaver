module
public import RankHullParameterizedSingleton
@[expose] public section
namespace ZFR

def bumpN : Nat → Formula → Formula
 | 0, p => p
 | n+1, p => bumpPredicate (bumpN n p)

def diagonalBody (psi : Formula) : Formula := .all (.imp (.mem 0 1)
 (.ex (.and (bumpPredicate psi)
   (.all (.imp (.all (.imp (.mem 0 1) (.mem 0 1)))
     (.all (.imp (bumpN 3 psi) (.ex (.and (bumpN 4 psi) (.mem 0 5))))))))))

theorem nd_vacuous_double (Γ : Context) (A B F : Formula) (h : ND (.seq Γ F)) :
 ND (.seq Γ (.all (.imp A (.all (.imp B (shift (shift F))))))) := by
 apply ND.allI
 apply ND.ii
 apply ND.allI
 apply ND.ii
 exact nd_weaken_head (nd_shift (nd_weaken_head (b := A) (nd_shift h)))

theorem diagonal_witness_subst (psi : Formula) :
 subst 0 (.and (bumpPredicate psi)
   (.all (.imp (.all (.imp (.mem 0 1) (.mem 0 1)))
     (.all (.imp (bumpN 3 psi) (.ex (.and (bumpN 4 psi) (.mem 0 5)))))))) =
 .and psi (.all (.imp (.all (.imp (.mem 0 1) (.mem 0 1)))
   (.all (.imp (bumpN 2 psi) (shift (shift (.ex (.and (bumpPredicate psi) (.mem 0 2))))))))) := by
 unfold subst
 simp only [rename,bumpN,bumpPredicate,shift,rename_comp]
 congr 4
 all_goals try rfl
 · have he : substMap 0 ∘ lift Nat.succ = id := by funext i; cases i <;> rfl
   rw [he,rename_id]
 · congr 1
   · apply congrArg (fun σ => rename σ psi)
     funext i; cases i <;> rfl
   · congr 2
     apply congrArg (fun σ => rename σ psi)
     funext i; cases i <;> rfl


theorem nd_diagonalBody {Γ : Context} (psi : Formula)
 (h : ND (.seq Γ (.all (.imp (.mem 0 1) psi)))) : ND (.seq Γ (diagonalBody psi)) := by
 apply ND.allI
 apply ND.ii
 let Δ := .mem 0 1 :: shiftContext Γ
 have hh : ND (.seq Δ (.all (.imp (.mem 0 2) (bumpPredicate psi)))) :=
   nd_weaken_head (nd_shift h)
 have hp : ND (.seq Δ psi) := by
   have ht := ND.ie (ND.allE 0 hh) (ND.ctx (a := .mem 0 1) (by simp [Δ]))
   change ND (.seq Δ (subst 0 (bumpPredicate psi))) at ht
   simpa only [bumpPredicate_subst] using ht
 have hm : ND (.seq Δ (.mem 0 1)) := ND.ctx (by simp [Δ])
 have he : ND (.seq Δ (.ex (.and (bumpPredicate psi) (.mem 0 2)))) := by
   apply ND.exI 0
   change ND (.seq Δ (.and (subst 0 (bumpPredicate psi)) (.mem 0 1)))
   rw [bumpPredicate_subst]
   exact ND.ci hp hm
 apply ND.exI 0
 rw [diagonal_witness_subst]
 exact ND.ci hp (nd_vacuous_double Δ _ _ _ he)

def diagonalPointedBody (i : Nat) (phi : Formula) := Formula.and
 (diagonalBody (bumpPredicate phi))
 (.imp (subst (i+1) (bumpPredicate phi)) (.mem (i+1) 0))

theorem shift_diagonalPointedEx (i : Nat) (phi : Formula) :
 shift (.ex (diagonalPointedBody i phi)) =
 .ex (diagonalPointedBody (i+1) (bumpPredicate phi)) := by
 simp only [shift,diagonalPointedBody,diagonalBody,rename,rename_subst,bumpN,
   bumpPredicate,rename_comp]
 simp only [Formula.ex.injEq,Formula.and.injEq,Formula.all.injEq,Formula.imp.injEq]
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals try {apply congrArg (fun σ => rename σ phi); funext j; cases j <;> rfl}
 all_goals try {congr 1; apply congrArg (fun σ => rename σ phi); funext j; cases j <;> rfl}

theorem subst_diagonalPointedBody (i : Nat) (phi : Formula) :
 subst 0 (diagonalPointedBody i phi) =
 .and (diagonalBody phi) (.imp (subst i phi) (.mem i 0)) := by
 simp only [subst,diagonalPointedBody,diagonalBody,rename,bumpN,bumpPredicate,rename_comp]
 simp only [Formula.ex.injEq,Formula.and.injEq,Formula.all.injEq,Formula.imp.injEq]
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals repeat constructor
 all_goals try {apply congrArg (fun σ => rename σ phi); funext j; cases j <;> rfl}

theorem nd_pointed_to_diagonal {Γ : Context} (i : Nat) (phi : Formula)
 (h : ND (.seq Γ (.ex (parameterizedPointedBody i phi)))) :
 ND (.seq Γ (.ex (diagonalPointedBody i phi))) := by
 apply ND.exE h
 let Δ := parameterizedPointedBody i phi :: shiftContext Γ
 have hh : ND (.seq Δ (parameterizedPointedBody i phi)) := ND.ctx (by simp [Δ])
 have hd := nd_diagonalBody (bumpPredicate phi) (ND.ce1 hh)
 have hp := ND.ce2 hh
 rw [shift_diagonalPointedEx]
 apply ND.exI 0
 rw [subst_diagonalPointedBody]
 exact ND.ci hd hp

theorem parameterized_diagonal_certificate (n : Nat) (phi : Formula) (hphi : Bound phi (n+1)) (i : Nat) :
 ClosedSeparation (separationSchema n phi) ∧
 ClosedContext (parameterizedSeparationContext n phi) ∧
 ND (.seq (parameterizedSeparationContext n phi) (.ex (diagonalPointedBody i phi))) := by
 obtain ⟨ha,hc,hd⟩ := parameterized_singleton_certificate n phi hphi i
 exact ⟨ha,hc,nd_pointed_to_diagonal i phi hd⟩

end ZFR
