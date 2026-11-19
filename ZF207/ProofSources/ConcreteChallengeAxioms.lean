module
public import ConcreteChallengeSyntax
public import DirectWitnessCoverage
public import SourceFoundationProofEquivalence
@[expose] public section
/-! Checked exact copied axiom and source provability correspondence. -/
namespace PalomarZF207
@[simp] theorem toSource_fixedRefl : toSource fixedRefl=ZFR.fixedRefl := rfl
@[simp] theorem toSource_fixedSym : toSource fixedSym=ZFR.fixedSym := rfl
@[simp] theorem toSource_fixedTrans : toSource fixedTrans=ZFR.fixedTrans := rfl
@[simp] theorem toSource_fixedEqElem : toSource fixedEqElem=ZFR.fixedEqElem := rfl
@[simp] theorem toSource_fixedExt : toSource fixedExt=ZFR.fixedExt := rfl
@[simp] theorem toSource_fixedEmpty : toSource fixedEmpty=ZFR.fixedEmpty := rfl
@[simp] theorem toSource_fixedPair : toSource fixedPair=ZFR.fixedPair := rfl
@[simp] theorem toSource_fixedUnion : toSource fixedUnion=ZFR.fixedUnion := rfl
@[simp] theorem toSource_fixedPower : toSource fixedPower=ZFR.fixedPower := rfl
@[simp] theorem toSource_fixedOmega : toSource fixedOmega=ZFR.fixedOmega := rfl
@[simp] theorem toSource_fixedFoundation : toSource fixedFoundation=ZFR.fixedFoundation := rfl
@[simp] theorem toSource_allPrefix (n:Nat)(p:Formula) :
 toSource (allPrefix n p)=ZFR.allPrefix n (toSource p) := by
 induction n <;> simp_all [allPrefix,ZFR.allPrefix,toSource]
@[simp] theorem toSource_separationSchema (n:Nat)(p:Formula):
 toSource (separationSchema n p)=ZFR.separationSchema n (toSource p) := by
 simp only [separationSchema,ZFR.separationSchema,toSource_allPrefix,
 separationFormula,ZFR.separationFormula,sourceIff,ZFR.sourceIff,toSource,toSource_rename]
 rfl
@[simp] theorem toSource_replacementSchema (n:Nat)(p:Formula):
 toSource (replacementSchema n p)=ZFR.replacementSchema n (toSource p) := by
 simp only [replacementSchema,ZFR.replacementSchema,toSource_allPrefix,
 replacementFormula,ZFR.replacementFormula,functionalityFormula,ZFR.functionalityFormula,
 sourceIff,ZFR.sourceIff,toSource,toSource_rename]
 rfl
theorem fixedAxiom_iff (p:Formula):FixedAxiom p ↔ ZFR.sourceZfrFixed (ZFR.encodeFormula (toSource p)) := by
 simp only [FixedAxiom,ZFR.sourceZfrFixed]
 simp only [← toSource_fixedRefl,← toSource_fixedSym,← toSource_fixedTrans,← toSource_fixedEqElem,← toSource_fixedExt,← toSource_fixedEmpty,← toSource_fixedPair,← toSource_fixedUnion,← toSource_fixedPower,← toSource_fixedOmega,← toSource_fixedFoundation,ZFR.encodeFormula_injective.eq_iff,toSource_injective.eq_iff]
theorem axiom_iff (p:Formula):Axiom p ↔ ZFR.sourceZfrAxiom (ZFR.encodeFormula (toSource p)) := by
 constructor
 · rintro (hf|⟨n,b,hb,rfl⟩|⟨n,b,hb,rfl⟩)
   · exact Or.inl ((fixedAxiom_iff p).mp hf)
   · rw [toSource_separationSchema]
     exact ZFR.separationSchema_in_zfr n (toSource b) ((toSource_bound b _).mpr hb)
   · rw [toSource_replacementSchema]
     exact ZFR.replacementSchema_in_zfr n (toSource b) ((toSource_bound b _).mpr hb)
 · rintro (hf|hs|hr)
   · exact Or.inl ((fixedAxiom_iff p).mpr hf)
   · obtain ⟨_,phi,n,hphi,he⟩ := hs
     obtain ⟨b,hb,hbound⟩ := RosserDirect.WitnessCoverage.bounded_code_is_formula phi (n+1) hphi
     rw [←hb,ZFR.numericSeparationCode_encode] at he
     refine Or.inr (Or.inl ⟨n,ofSource b,(ofSource_bound b _).mpr hbound,?_⟩)
     apply toSource_injective
     simpa only [toSource_separationSchema,toSource_ofSource] using ZFR.encodeFormula_injective he
   · obtain ⟨_,phi,n,hphi,he⟩ := hr
     obtain ⟨b,hb,hbound⟩ := RosserDirect.WitnessCoverage.bounded_code_is_formula phi (n+2) hphi
     rw [←hb,ZFR.numericReplacementCode_encode] at he
     refine Or.inr (Or.inr ⟨n,ofSource b,(ofSource_bound b _).mpr hbound,?_⟩)
     apply toSource_injective
     simpa only [toSource_replacementSchema,toSource_ofSource] using ZFR.encodeFormula_injective he

theorem provable_iff (p:Formula):Provable p ↔ RosserDirect.ZFDriver.SourceCertificate (toSource p) := by
 constructor
 · rintro ⟨Γ,hΓ,hd⟩
   refine ⟨toSourceContext Γ,?_,toSource_nd hd⟩
   intro q hq
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hq
   exact (axiom_iff a).mp (hΓ a ha)
 · rintro ⟨Γ,hΓ,hd⟩
   refine ⟨ofSourceContext Γ,?_,?_⟩
   · intro q hq
     obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hq
     apply (axiom_iff (ofSource a)).mpr
     simpa only [toSource_ofSource] using hΓ a ha
   · have hh:=ofSource_nd hd
     simpa only [ofSourceRow,ofSource_toSource] using hh
end PalomarZF207
