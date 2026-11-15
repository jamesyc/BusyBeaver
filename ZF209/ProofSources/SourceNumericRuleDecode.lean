module
public import SourceNumericDecode
@[expose] public section
namespace ZFR.NumericDecode
open C209Soundness
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

@[simp] theorem wf_and (a b : Nat) : sourceWf (sourceNode 3 a b) ↔ sourceWf a ∧ sourceWf b := by
 simpa using sourceWf_node 3 a b (by decide) (by decide)
@[simp] theorem wf_or (a b : Nat) : sourceWf (sourceNode 4 a b) ↔ sourceWf a ∧ sourceWf b := by
 simpa using sourceWf_node 4 a b (by decide) (by decide)
@[simp] theorem wf_imp (a b : Nat) : sourceWf (sourceNode 5 a b) ↔ sourceWf a ∧ sourceWf b := by
 simpa using sourceWf_node 5 a b (by decide) (by decide)
@[simp] theorem wf_all (a : Nat) : sourceWf (sourceNode 6 a 0) ↔ sourceWf a := by
 simpa using sourceWf_node 6 a 0 (by decide) (by decide)
@[simp] theorem wf_ex (a : Nat) : sourceWf (sourceNode 7 a 0) ↔ sourceWf a := by
 simpa using sourceWf_node 7 a 0 (by decide) (by decide)

attribute [local irreducible] sourceContextShift sourceSubst sourceShift df dc dr sourceSequent sourceBranches sourceNode sourceCons

/-- Numeric base-rule acceptance yields a genuine typed derivation. -/
theorem base_sound {r : Nat} (h : sourceBase r) : ND (dr r) := by
 rcases h with ⟨hw,⟨g,a,rfl,hm⟩ | ⟨g,a,b,rfl⟩⟩
 · rw [dr_seq]
   apply ND.ctx
   exact (show df a ∈ dc g from by
    rw [dc]; exact List.mem_map.mpr ⟨a,hm,rfl⟩)
 · have hw' := (wf_seq _ _).mp hw
   simp only [wf_imp] at hw'
   obtain ⟨hg,⟨⟨ha,hb⟩,_⟩,_⟩ := hw'
   have hab := node_wf 5 a b (by simp) ha hb
   have haba := node_wf 5 (sourceNode 5 a b) a (by simp) hab ha
   rw [dr_seq,df_imp haba ha,df_imp hab ha,df_imp ha hb]
   exact ND.pc _ _ _

theorem unary_ii (g a b : Nat) (hw : sourceRowWf (sourceSequent g (sourceNode 5 a b))) (hp : sourceRowWf (sourceSequent (sourceCons a g) b))
 (hn : ND (dr (sourceSequent (sourceCons a g) b))) : ND (dr (sourceSequent g (sourceNode 5 a b))) := by
 have hab := (wf_imp a b).mp ((wf_seq g (sourceNode 5 a b)).mp hw).2
 rw [dr_seq,df_imp hab.1 hab.2]
 rw [dr_seq,dc_cons] at hn
 exact ND.ii hn

theorem unary_exp (g a : Nat) (hw : sourceRowWf (sourceSequent g a)) (hp : sourceRowWf (sourceSequent g 0))
 (hn : ND (dr (sourceSequent g 0))) : ND (dr (sourceSequent g a)) := by
 rw [dr_seq,df_zero] at hn
 rw [dr_seq]
 exact ND.exp hn

theorem unary_ce1 (g a b : Nat) (hw : sourceRowWf (sourceSequent g a)) (hp : sourceRowWf (sourceSequent g (sourceNode 3 a b)))
 (hn : ND (dr (sourceSequent g (sourceNode 3 a b)))) : ND (dr (sourceSequent g a)) := by
 have hab := (wf_and a b).mp ((wf_seq g (sourceNode 3 a b)).mp hp).2
 rw [dr_seq,df_and hab.1 hab.2] at hn
 rw [dr_seq]
 exact ND.ce1 hn

theorem unary_ce2 (g a b : Nat) (hw : sourceRowWf (sourceSequent g b)) (hp : sourceRowWf (sourceSequent g (sourceNode 3 a b)))
 (hn : ND (dr (sourceSequent g (sourceNode 3 a b)))) : ND (dr (sourceSequent g b)) := by
 have hab := (wf_and a b).mp ((wf_seq g (sourceNode 3 a b)).mp hp).2
 rw [dr_seq,df_and hab.1 hab.2] at hn
 rw [dr_seq]
 exact ND.ce2 hn

theorem unary_di1 (g a b : Nat) (hw : sourceRowWf (sourceSequent g (sourceNode 4 a b))) (hp : sourceRowWf (sourceSequent g a))
 (hn : ND (dr (sourceSequent g a))) : ND (dr (sourceSequent g (sourceNode 4 a b))) := by
 have hab := (wf_or a b).mp ((wf_seq g (sourceNode 4 a b)).mp hw).2
 rw [dr_seq,df_or hab.1 hab.2]
 rw [dr_seq] at hn
 exact ND.di1 hn

theorem unary_di2 (g a b : Nat) (hw : sourceRowWf (sourceSequent g (sourceNode 4 a b))) (hp : sourceRowWf (sourceSequent g b))
 (hn : ND (dr (sourceSequent g b))) : ND (dr (sourceSequent g (sourceNode 4 a b))) := by
 have hab := (wf_or a b).mp ((wf_seq g (sourceNode 4 a b)).mp hw).2
 rw [dr_seq,df_or hab.1 hab.2]
 rw [dr_seq] at hn
 exact ND.di2 hn

theorem unary_wk (g j a : Nat) (hw : sourceRowWf (sourceSequent j a)) (hp : sourceRowWf (sourceSequent g a))
 (hn : ND (dr (sourceSequent g a))) (hs : sourceContextSub g j) : ND (dr (sourceSequent j a)) := by
 rw [dr_seq] at hn ⊢
 exact ND.wk (dc_sub hs) hn

theorem unary_allI (g a : Nat) (hw : sourceRowWf (sourceSequent g (sourceNode 6 a 0))) (hp : sourceRowWf (sourceSequent (sourceContextShift g) a))
 (hn : ND (dr (sourceSequent (sourceContextShift g) a))) : ND (dr (sourceSequent g (sourceNode 6 a 0))) := by
 have ha := (wf_all a).mp ((wf_seq g (sourceNode 6 a 0)).mp hw).2
 have hg := ((wf_seq g (sourceNode 6 a 0)).mp hw).1
 rw [dr_seq,df_all ha]
 rw [dr_seq,dc_shift hg] at hn
 exact ND.allI hn

theorem unary_allE (g a t : Nat) (hw : sourceRowWf (sourceSequent g (sourceSubst 0 t a))) (hp : sourceRowWf (sourceSequent g (sourceNode 6 a 0)))
 (hn : ND (dr (sourceSequent g (sourceNode 6 a 0)))) : ND (dr (sourceSequent g (sourceSubst 0 t a))) := by
 have ha := (wf_all a).mp ((wf_seq g (sourceNode 6 a 0)).mp hp).2
 rw [dr_seq,df_all ha] at hn
 rw [dr_seq,df_subst ha]
 exact ND.allE t hn

theorem unary_exI (g a t : Nat) (hw : sourceRowWf (sourceSequent g (sourceNode 7 a 0))) (hp : sourceRowWf (sourceSequent g (sourceSubst 0 t a)))
 (hn : ND (dr (sourceSequent g (sourceSubst 0 t a)))) : ND (dr (sourceSequent g (sourceNode 7 a 0))) := by
 have ha := (wf_ex a).mp ((wf_seq g (sourceNode 7 a 0)).mp hw).2
 rw [dr_seq,df_ex ha]
 rw [dr_seq,df_subst ha] at hn
 exact ND.exI t hn

theorem binary_ie (g a b : Nat) (hw : sourceRowWf (sourceSequent g b)) (hp : sourceRowWf (sourceSequent g (sourceNode 5 a b))) (hq : sourceRowWf (sourceSequent g a))
 (hn : ND (dr (sourceSequent g (sourceNode 5 a b)))) (hm : ND (dr (sourceSequent g a))) : ND (dr (sourceSequent g b)) := by
 have hab := (wf_imp a b).mp ((wf_seq g (sourceNode 5 a b)).mp hp).2
 rw [dr_seq,df_imp hab.1 hab.2] at hn
 rw [dr_seq] at hm ⊢
 exact ND.ie hn hm

theorem binary_ci (g a b : Nat) (hw : sourceRowWf (sourceSequent g (sourceNode 3 a b))) (hp : sourceRowWf (sourceSequent g a)) (hq : sourceRowWf (sourceSequent g b))
 (hn : ND (dr (sourceSequent g a))) (hm : ND (dr (sourceSequent g b))) : ND (dr (sourceSequent g (sourceNode 3 a b))) := by
 have hab := (wf_and a b).mp ((wf_seq g (sourceNode 3 a b)).mp hw).2
 rw [dr_seq,df_and hab.1 hab.2]
 rw [dr_seq] at hn hm
 exact ND.ci hn hm

theorem binary_branchPair (g a b c : Nat) (hw : sourceRowWf (sourceBranches g a b c)) (hp : sourceRowWf (sourceSequent (sourceCons a g) c)) (hq : sourceRowWf (sourceSequent (sourceCons b g) c))
 (hn : ND (dr (sourceSequent (sourceCons a g) c))) (hm : ND (dr (sourceSequent (sourceCons b g) c))) : ND (dr (sourceBranches g a b c)) := by
 rw [dr_seq,dc_cons] at hn hm
 rw [dr_branches]
 exact ND.branchPair hn hm

theorem binary_de (g a b c : Nat) (hw : sourceRowWf (sourceSequent g c)) (hp : sourceRowWf (sourceSequent g (sourceNode 4 a b))) (hq : sourceRowWf (sourceBranches g a b c))
 (hn : ND (dr (sourceSequent g (sourceNode 4 a b)))) (hm : ND (dr (sourceBranches g a b c))) : ND (dr (sourceSequent g c)) := by
 have hab := (wf_or a b).mp ((wf_seq g (sourceNode 4 a b)).mp hp).2
 rw [dr_seq,df_or hab.1 hab.2] at hn
 rw [dr_branches] at hm
 rw [dr_seq]
 exact ND.de hn hm

theorem binary_exE (g a c : Nat) (hw : sourceRowWf (sourceSequent g c)) (hp : sourceRowWf (sourceSequent g (sourceNode 7 a 0))) (hq : sourceRowWf (sourceSequent (sourceCons a (sourceContextShift g)) (sourceShift 0 c)))
 (hn : ND (dr (sourceSequent g (sourceNode 7 a 0)))) (hm : ND (dr (sourceSequent (sourceCons a (sourceContextShift g)) (sourceShift 0 c)))) : ND (dr (sourceSequent g c)) := by
 have ha := (wf_ex a).mp ((wf_seq g (sourceNode 7 a 0)).mp hp).2
 have hg := ((wf_seq g c).mp hw).1
 have hc := ((wf_seq g c).mp hw).2
 rw [dr_seq,df_ex ha] at hn
 rw [dr_seq,dc_cons,dc_shift hg,df_shift hc] at hm
 rw [dr_seq]
 exact ND.exE hn hm

/-- Prior-row well-formedness is explicit; decoding a malformed numeral to a
fallback formula never licenses a proof step. -/
theorem unary_sound {p r : Nat} (hp : sourceRowWf p) (hn : ND (dr p))
 (h : sourceUnary p r) : ND (dr r) := by
 rcases h with ⟨hw,h⟩
 rcases h with ⟨g,a,b,rfl,rfl⟩ | ⟨g,a,rfl,rfl⟩ | ⟨g,a,b,rfl,rfl⟩ |
  ⟨g,a,b,rfl,rfl⟩ | ⟨g,a,b,rfl,rfl⟩ | ⟨g,a,b,rfl,rfl⟩ |
  ⟨g,j,a,rfl,rfl,hs⟩ | ⟨g,a,rfl,rfl⟩ | ⟨g,a,t,rfl,rfl⟩ | ⟨g,a,t,rfl,rfl⟩
 · exact unary_ii g a b hw hp hn
 · exact unary_exp g a hw hp hn
 · exact unary_ce1 g a b hw hp hn
 · exact unary_ce2 g a b hw hp hn
 · exact unary_di1 g a b hw hp hn
 · exact unary_di2 g a b hw hp hn
 · exact unary_wk g j a hw hp hn hs
 · exact unary_allI g a hw hp hn
 · exact unary_allE g a t hw hp hn
 · exact unary_exI g a t hw hp hn

/-- Every accepted binary numeric rule reconstructs its typed ND constructor. -/
theorem binary_sound {p q r : Nat} (hp : sourceRowWf p) (hq : sourceRowWf q)
 (hn : ND (dr p)) (hm : ND (dr q)) (h : sourceBinary p q r) : ND (dr r) := by
 rcases h with ⟨hw,h⟩
 rcases h with ⟨g,a,b,rfl,rfl,rfl⟩ | ⟨g,a,b,rfl,rfl,rfl⟩ |
  ⟨g,a,b,c,rfl,rfl,rfl⟩ | ⟨g,a,b,c,rfl,rfl,rfl⟩ | ⟨g,a,c,rfl,rfl,rfl⟩
 · exact binary_ie g a b hw hp hq hn hm
 · exact binary_ci g a b hw hp hq hn hm
 · exact binary_branchPair g a b c hw hp hq hn hm
 · exact binary_de g a b c hw hp hq hn hm
 · exact binary_exE g a c hw hp hq hn hm

end ZFR.NumericDecode
