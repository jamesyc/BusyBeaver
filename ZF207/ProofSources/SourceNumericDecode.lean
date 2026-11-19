module
public import DirectWitnessCoverage
@[expose] public section
namespace ZFR.NumericDecode
open C207Soundness
set_option backward.isDefEq.respectTransparency false

theorem wf_has_formula (n : Nat) (hw : sourceWf n) : ∃ p : Formula, encodeFormula p = n := by
 induction n using Nat.strong_induction_on with
 | h n ih =>
   by_cases hn : n=0
   · subst n; exact ⟨.bot,rfl⟩
   have hsmall : n/8<n := Nat.div_lt_self (by omega) (by omega)
   have ha : (unpair (n/8)).1<n := Nat.lt_of_le_of_lt (unpair_left_le _) hsmall
   have hb : (unpair (n/8)).2<n := Nat.lt_of_le_of_lt (unpair_right_le _) hsmall
   have rebuild : sourceNode (n%8) (unpair (n/8)).1 (unpair (n/8)).2=n := by
    unfold sourceNode; rw [unpair_spec]; omega
   rw [sourceWf] at hw
   simp only [hn,dite_false] at hw
   rcases hw with ht | ⟨ht,hx,hy⟩ | ⟨ht,hy,hx⟩
   · rcases ht with ht | ht
     · exact ⟨.mem _ _,by simpa [encodeFormula,ht] using rebuild⟩
     · exact ⟨.eq _ _,by simpa [encodeFormula,ht] using rebuild⟩
   · obtain ⟨a,hea⟩ := ih _ ha hx
     obtain ⟨b,heb⟩ := ih _ hb hy
     rcases ht with ht | ht | ht
     · exact ⟨.and a b,by simpa [encodeFormula,hea,heb,ht] using rebuild⟩
     · exact ⟨.or a b,by simpa [encodeFormula,hea,heb,ht] using rebuild⟩
     · exact ⟨.imp a b,by simpa [encodeFormula,hea,heb,ht] using rebuild⟩
   · obtain ⟨a,hea⟩ := ih _ ha hx
     rcases ht with ht | ht
     · exact ⟨.all a,by simpa [encodeFormula,hea,hy,ht] using rebuild⟩
     · exact ⟨.ex a,by simpa [encodeFormula,hea,hy,ht] using rebuild⟩

attribute [local instance] Classical.propDecidable
noncomputable def df (n : Nat) : Formula := if h : sourceWf n then Classical.choose (wf_has_formula n h) else .bot
theorem encode_df {n : Nat} (h : sourceWf n) : encodeFormula (df n)=n := by
 simp only [df,dif_pos h]; exact Classical.choose_spec (wf_has_formula n h)
@[simp] theorem df_encode (p : Formula) : df (encodeFormula p)=p :=
 encodeFormula_injective (encode_df (sourceWf_encodeFormula p))
@[simp] theorem df_zero : df 0=.bot := df_encode .bot

theorem node_wf (t a b : Nat) (ht : t=3 ∨ t=4 ∨ t=5) (ha : sourceWf a) (hb : sourceWf b) :
 sourceWf (sourceNode t a b) := by
 rcases ht with rfl | rfl | rfl <;> rw [sourceWf_node _ _ _ (by decide) (by decide)] <;> simp_all

theorem df_and {a b : Nat} (ha : sourceWf a) (hb : sourceWf b) :
 df (sourceNode 3 a b)=.and (df a) (df b) := by
 apply encodeFormula_injective
 rw [encode_df (node_wf _ _ _ (by simp) ha hb),encodeFormula,encode_df ha,encode_df hb]
theorem df_or {a b : Nat} (ha : sourceWf a) (hb : sourceWf b) :
 df (sourceNode 4 a b)=.or (df a) (df b) := by
 apply encodeFormula_injective
 rw [encode_df (node_wf _ _ _ (by simp) ha hb),encodeFormula,encode_df ha,encode_df hb]
theorem df_imp {a b : Nat} (ha : sourceWf a) (hb : sourceWf b) :
 df (sourceNode 5 a b)=.imp (df a) (df b) := by
 apply encodeFormula_injective
 rw [encode_df (node_wf _ _ _ (by simp) ha hb),encodeFormula,encode_df ha,encode_df hb]
theorem df_all {a : Nat} (ha : sourceWf a) : df (sourceNode 6 a 0)=.all (df a) := by
 have hw : sourceWf (sourceNode 6 a 0) := by rw [sourceWf_node _ _ _ (by decide) (by decide)]; simp [ha]
 apply encodeFormula_injective
 rw [encode_df hw,encodeFormula,encode_df ha]
theorem df_ex {a : Nat} (ha : sourceWf a) : df (sourceNode 7 a 0)=.ex (df a) := by
 have hw : sourceWf (sourceNode 7 a 0) := by rw [sourceWf_node _ _ _ (by decide) (by decide)]; simp [ha]
 apply encodeFormula_injective
 rw [encode_df hw,encodeFormula,encode_df ha]

noncomputable def dc (g : Nat) : Context := (decodeSourceList g).map df
@[simp] theorem dc_zero : dc 0=[] := by simp [dc,decodeSourceList_zero]
@[simp] theorem dc_cons (a g : Nat) : dc (sourceCons a g)=df a::dc g := by
 simp [dc,sourceCons,decodeSourceList_cons]
@[simp] theorem dc_encode (Γ : Context) : dc (encodeContext Γ)=Γ := by
 simp [dc,encodeContext,decodeSourceList_encode,List.map_map,Function.comp_def]
theorem encode_decodeList (n : Nat) : encodeList id (decodeSourceList n)=n := by
 induction n using Nat.strong_induction_on with
 | h n ih =>
   by_cases hn : n=0
   · subst n; simp [decodeSourceList_zero,encodeList]
   have hh := unpair_right_le (n-1)
   rw [decodeSourceList]
   simp only [hn,dite_false,encodeList,id_eq]
   rw [ih _ (by omega),unpair_spec]
   omega
theorem encode_dc {g : Nat} (hg : sourceContextWf g) : encodeContext (dc g)=g := by
 rw [dc,encodeContext,encodeList_map]
 have he : encodeList (encodeFormula ∘ df) (decodeSourceList g)=encodeList id (decodeSourceList g) := by
   have aux : ∀ xs : List Nat, (∀ a ∈ xs, sourceWf a) →
     encodeList (encodeFormula ∘ df) xs=encodeList id xs := by
    intro xs hx
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      simp only [encodeList,Function.comp_def,id_eq]
      rw [encode_df (hx a (by simp))]
      exact congrArg (fun k => cantor a k+1) (ih (fun b hb => hx b (by simp [hb])))
   exact aux _ hg
 exact he.trans (encode_decodeList g)
noncomputable def dr (r : Nat) : Row :=
 let p := unpair r
 let q := unpair p.2
 if p.1=0 then .seq (dc q.1) (df q.2)
 else .branches (dc q.1) (df (unpair q.2).1)
   (df (unpair (unpair q.2).2).1) (df (unpair (unpair q.2).2).2)
@[simp] theorem dr_seq (g a : Nat) : dr (sourceSequent g a)=.seq (dc g) (df a) := by
 simp [dr,sourceSequent,sourceUnpair_pair]
@[simp] theorem dr_branches (g a b c : Nat) : dr (sourceBranches g a b c)=.branches (dc g) (df a) (df b) (df c) := by
 simp [dr,sourceBranches,sourceUnpair_pair]
@[simp] theorem dr_encode (r : Row) : dr (encodeRow r)=r := by
 cases r <;> simp [dr,encodeRow,sourceUnpair_pair]
theorem df_shift {a : Nat} (ha : sourceWf a) : df (sourceShift 0 a)=shift (df a) := by
 have he := sourceShift_encode (df a)
 rw [encode_df ha] at he
 rw [he,df_encode]
theorem df_subst {a : Nat} (ha : sourceWf a) (t : Nat) : df (sourceSubst 0 t a)=subst t (df a) := by
 have he := sourceSubst_encode t (df a)
 rw [encode_df ha] at he
 rw [he,df_encode]
theorem dc_shift {g : Nat} (hg : sourceContextWf g) : dc (sourceContextShift g)=shiftContext (dc g) := by
 have he := sourceContextShift_encode (dc g)
 rw [encode_dc hg] at he
 rw [he,dc_encode]
theorem dc_sub {g h : Nat} (hh : sourceContextSub g h) : ContextSub (dc g) (dc h) := by
 intro p hp
 obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
 exact List.mem_map.mpr ⟨a,hh a ha,rfl⟩
@[simp] theorem wf_seq (g a : Nat) : sourceRowWf (sourceSequent g a) ↔ sourceContextWf g ∧ sourceWf a := by
 simp [sourceRowWf,sourceSequent,sourceUnpair_pair]
@[simp] theorem wf_branches (g a b c : Nat) : sourceRowWf (sourceBranches g a b c) ↔
 sourceContextWf g ∧ sourceWf a ∧ sourceWf b ∧ sourceWf c := by
 simp [sourceRowWf,sourceBranches,sourceUnpair_pair]
end ZFR.NumericDecode
