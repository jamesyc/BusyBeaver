module
public import DiagonalGateEndpoint
@[expose] public section
namespace ZFR
open C207Soundness

def positiveMemberSource (A : C207Soundness.Formula) (a d h : Nat) (ρ : Nat → Nat) : Formula :=
 let rh := bindName h ρ
 let rd := bindName d rh
 let ru := bindName d rd
 let rs := bindName a ru
 let rv := bindName h ru
 let rw := bindName h rv
 .all (.imp (.mem (rh h) (rh a)) (.ex (.and (translate rd A)
   (.all (.imp (.all (.imp (.mem (rs a) (rs d)) (.mem (rs a) (rs h))))
    (.all (.imp (translate rv A) (.ex (.and (translate rw A) (.mem (rw h) (rw a)))))))))))

def rawMemberSource (A : C207Soundness.Formula) (a d h : Nat) (ρ : Nat → Nat) : Formula :=
 let rh := bindName h ρ
 let rd := bindName d rh
 let ru := bindName d rd
 let rs := bindName a ru
 let rv := bindName h ru
 let rw := bindName h rv
 .all (.imp (.mem (rh h) (rh a)) (.imp (.all (.imp (translate rd A)
   (.imp (.all (.imp (.all (.imp (.mem (rs a) (rs d)) (.mem (rs a) (rs h))))
    (.all (.imp (translate rv A) (.imp (.all (.imp (translate rw A)
      (.imp (.mem (rw h) (rw a)) .bot))) .bot))))) .bot))) .bot))

def positivePointedSource (a d h : Nat) : Formula :=
 let rc := bindName a id
 .ex (.and (positiveMemberSource (decodeNat a) a d h rc)
   (.imp (translate rc (decodeNat a)) (.mem (rc h) (rc a))))

def rawPointedUniversal (a d h : Nat) : Formula :=
 let rc := bindName a id
 .all (.imp (rawMemberSource (decodeNat a) a d h rc)
   (.imp (.imp (translate rc (decodeNat a)) (.mem (rc h) (rc a))) .bot))

theorem positiveMember_raw_equiv (Γ : Context) (A : C207Soundness.Formula)
 (a d h : Nat) (ρ : Nat → Nat) :
 NDEquiv Γ (positiveMemberSource A a d h ρ) (rawMemberSource A a d h ρ) := by
 unfold positiveMemberSource rawMemberSource
 apply NDEquiv.all
 apply NDEquiv.imp (NDEquiv.refl _ _)
 apply ex_and_encoding_congr
 apply NDEquiv.all
 apply NDEquiv.imp (NDEquiv.refl _ _)
 apply NDEquiv.all
 apply NDEquiv.imp (NDEquiv.refl _ _)
 exact NDEquiv.ex_and_encoding _ _ _

theorem positivePointed_raw_equiv (Γ : Context) (a d h : Nat) :
 NDEquiv Γ (positivePointedSource a d h) (.imp (rawPointedUniversal a d h) .bot) := by
 unfold positivePointedSource rawPointedUniversal
 apply (NDEquiv.ex_and_encoding Γ _ _).trans
 apply NDEquiv.imp
 · apply NDEquiv.all
   apply NDEquiv.imp (positiveMember_raw_equiv _ _ _ _ _ _)
   exact NDEquiv.refl _ _
 · exact NDEquiv.refl _ _

theorem botPointedGate_positive_shape (a d h : Nat) (had : a ≠ d) (hah : a ≠ h) :
 botPointedGate a d h id =
 .imp (.imp (vacuousAll (.eq h d)) (.imp (vacuousAll (.mem h d))
   (rawPointedUniversal a d h))) .bot := by
 simp only [botPointedGate,pointedGateTree,GateTree.toSource,botGateFalse,
  rawPointedUniversal,rawMemberSource,vacuousAll]
 simp [bindName,had,hah,Ne.symm had,Ne.symm hah,shift,rename]

/-- Uniform syntactic bridge, including the distinct-label case. The supplied
positive witness is an actual ND proof, not a semantic set existence claim. -/
theorem nd_positive_to_literal_gate (a d h : Nat) (had : a ≠ d) (hah : a ≠ h)
 {Γ : Context} (hc : ContextSub coreContext Γ)
 (hp : ND (.seq Γ (positivePointedSource a d h))) :
 ND (.seq Γ (translateCode id (pointedGateCode a d h))) := by
 have hr := ND.ie (positivePointed_raw_equiv Γ a d h).1 hp
 have hb : ND (.seq Γ (botPointedGate a d h id)) := by
   rw [botPointedGate_positive_shape a d h had hah]
   apply ND.ii
   apply ND.ie hr.weaken_cons
   exact ND.ie (ND.ie (ND.ctx (by simp)) (nd_vacuousAll _ (.eq h d)))
     (nd_vacuousAll _ (.mem h d))
 exact ND.ie (pointedGate_false_equiv a d h id hc).2 hb

theorem source_literal_gate_of_positive (a d h : Nat) (had : a ≠ d) (hah : a ≠ h)
 (hp : SourceTheorem (positivePointedSource a d h)) :
 SourceTheorem (translateCode id (pointedGateCode a d h)) := by
 obtain ⟨Γ,hΓ,hp⟩ := hp
 refine ⟨coreContext++Γ,?_,nd_positive_to_literal_gate a d h had hah
   (fun p hp => List.mem_append_left Γ hp)
   (ND.wk (fun p hp => List.mem_append_right coreContext hp) hp)⟩
 intro p hp
 rcases List.mem_append.mp hp with hc | hg
 · exact coreContext_in_zfr p hc
 · exact hΓ p hg

/-- Remaining mathematical obligation after all literal syntax is discharged. -/
def DistinctPositiveWitnessObligation : Prop := ∀ a d h,
 a ≠ d → a ≠ h → d ≠ h → SourceTheorem (positivePointedSource a d h)

theorem reverse_calibration_pending_positive_witness
 (hw : DistinctPositiveWitnessObligation) (h : ExactProvable 1) : ZfrProvable 0 := by
 apply reverse_calibration_pending_distinct_gate (h := h)
 intro a d h had hah hdh
 exact source_literal_gate_of_positive a d h had hah (hw a d h had hah hdh)

end ZFR
