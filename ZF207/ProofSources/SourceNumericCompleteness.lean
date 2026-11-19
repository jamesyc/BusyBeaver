module
public import SourceNumericTraceDecode
public import SourceNumericRuleDecode
public import DirectZFCompleteness
public import ZfrCoreEndpoints
@[expose] public section
namespace ZFR.NumericDecode
/-- Each accepted numeric row is well formed AND has a genuine typed ND proof.
Maintaining the well-formedness component is essential: default decoding of
malformed rows alone would not validate numeric-rule premise inversions. -/
def Good (r : Nat) := sourceRowWf r ∧ ND (dr r)
theorem rules_good (r xs : Nat) (hs : ∀ p, sourceMember p xs → Good p)
 (h : sourceFullRules r xs) : Good r := by
 rcases h with hb | ⟨p,hp,hu⟩ | ⟨p,q,hp,hq,hb⟩
 · exact ⟨hb.1,base_sound hb⟩
 · exact ⟨hu.1,unary_sound (hs p hp).1 (hs p hp).2 hu⟩
 · exact ⟨hb.1,binary_sound (hs p hp).1 (hs q hq).1 (hs p hp).2 (hs q hq).2 hb⟩
theorem derives_sound {p r : Nat} (h : sourceFullDerives p r) : Good r :=
 numeric_trace_induction Good rules_good p h.1 r h.2

/-- Exact reverse direction for all numeric source theorem witnesses. No
canonical-input restriction is assumed: it follows from numeric rule guards. -/
theorem numeric_to_source {f : Formula} (h : ZfrProvable (encodeFormula f)) :
 RosserDirect.ZFDriver.SourceCertificate f := by
 obtain ⟨g,p,hg,hd⟩ := h
 have good := derives_sound hd
 have hw := ((wf_seq _ _).mp good.1).1
 refine ⟨dc g,?_,?_⟩
 · intro a ha
   obtain ⟨n,hn,rfl⟩ := List.mem_map.mp ha
   rw [encode_df (hw n hn)]
   exact hg n hn
 · simpa only [dr_seq,df_encode] using good.2

theorem source_to_numeric {f : Formula} (h : RosserDirect.ZFDriver.SourceCertificate f) :
 ZfrProvable (encodeFormula f) := by
 obtain ⟨Γ,hΓ,hd⟩ := h
 exact hd.theoryProvable hΓ

end ZFR.NumericDecode
