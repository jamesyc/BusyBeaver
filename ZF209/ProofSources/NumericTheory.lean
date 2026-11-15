module
public import NumericBounds
public import CoreAxiomTemplates
public import RankHullSourceSchemas
public import ExactSourceDerives
@[expose] public section
namespace ZFR

def fixedRefl : Formula := (.all (.eq 0 0))

def fixedSym : Formula := (.all (.all (.imp (.eq 1 0) (.eq 0 1))))

def fixedTrans : Formula := (.all (.all (.all (.imp (.eq 2 1) (.imp (.eq 1 0) (.eq 2 0))))))

def fixedEqElem : Formula := (.all (.all (.all (.all (.imp (.eq 3 1) (.imp (.eq 2 0) (.imp (.mem 3 2) (.mem 1 0))))))))

def fixedExt : Formula := (.all (.all (.imp (.all (.imp (.mem 0 2) (.mem 0 1))) (.imp (.all (.imp (.mem 0 1) (.mem 0 2))) (.eq 1 0)))))

def fixedEmpty : Formula := (.ex (.all (.imp (.mem 0 1) (.bot))))

def fixedPair : Formula := (.all (.all (.ex (.all (.and (.imp (.mem 0 1) (.or (.eq 0 3) (.eq 0 2))) (.imp (.or (.eq 0 3) (.eq 0 2)) (.mem 0 1)))))))

def fixedUnion : Formula := (.all (.ex (.all (.and (.imp (.mem 0 1) (.ex (.and (.mem 0 3) (.mem 1 0)))) (.imp (.ex (.and (.mem 0 3) (.mem 1 0))) (.mem 0 1))))))

def fixedPower : Formula := (.all (.ex (.all (.and (.imp (.mem 0 1) (.all (.imp (.mem 0 1) (.mem 0 3)))) (.imp (.all (.imp (.mem 0 1) (.mem 0 3))) (.mem 0 1))))))

def fixedOmega : Formula := (.ex (.and (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.mem 0 2) (.mem 0 1)))))))

def fixedFoundation : Formula := (.all (.imp (.ex (.mem 0 1)) (.ex (.and (.mem 0 1) (.all (.imp (.mem 0 1) (.imp (.mem 0 2) (.bot))))))))

def sourceZfrFixed (n : Nat) : Prop :=
  n = encodeFormula fixedRefl ∨
  n = encodeFormula fixedSym ∨
  n = encodeFormula fixedTrans ∨
  n = encodeFormula fixedEqElem ∨
  n = encodeFormula fixedExt ∨
  n = encodeFormula fixedEmpty ∨
  n = encodeFormula fixedPair ∨
  n = encodeFormula fixedUnion ∨
  n = encodeFormula fixedPower ∨
  n = encodeFormula fixedOmega ∨
  n = encodeFormula fixedFoundation

theorem sourceZfrFixed_closed {n : Nat} (h : sourceZfrFixed n) : sourceBound 0 n := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [sourceBound_encode] <;> simp [fixedRefl,fixedSym,fixedTrans,fixedEqElem,fixedExt,fixedEmpty,fixedPair,fixedUnion,fixedPower,fixedOmega,fixedFoundation,Bound]

def numericIff (a b : Nat) := sourceNode 3 (sourceNode 5 a b) (sourceNode 5 b a)
def numericSeparation (b : Nat) := sourceNode 6 (sourceNode 7 (sourceNode 6
  (numericIff (sourceNode 1 0 1) (sourceNode 3 (sourceNode 1 0 2) b)) 0) 0) 0
def numericFunctionality (a b : Nat) := sourceNode 6 (sourceNode 6 (sourceNode 6
  (sourceNode 5 a (sourceNode 5 b (sourceNode 2 1 0))) 0) 0) 0
def numericReplacement (a b c : Nat) := sourceNode 5 (numericFunctionality a b)
  (sourceNode 6 (sourceNode 7 (sourceNode 6 (numericIff (sourceNode 1 0 1)
    (sourceNode 7 (sourceNode 3 (sourceNode 1 0 3) c) 0)) 0) 0) 0)
def numericAllPrefix : Nat → Nat → Nat
 | 0, a => a
 | n+1, a => sourceNode 6 (numericAllPrefix n a) 0

def numericSeparationCode (phi n : Nat) :=
 numericAllPrefix n (numericSeparation (sourceRename sepIndex 0 phi))
def numericReplacementCode (phi n : Nat) :=
 numericAllPrefix n (numericReplacement (sourceRename repAIndex 0 phi)
  (sourceRename repBIndex 0 phi) (sourceRename repCIndex 0 phi))
def numericClosedSeparation (z : Nat) := sourceBound 0 z ∧
 ∃ phi n, sourceBound (n+1) phi ∧ z = numericSeparationCode phi n
def numericClosedReplacement (z : Nat) := sourceBound 0 z ∧
 ∃ phi n, sourceBound (n+2) phi ∧ z = numericReplacementCode phi n

/-- Exact ZFR: ten fixed core axioms plus Foundation, Separation, Replacement.
Choice is deliberately absent. -/
def sourceZfrAxiom (z : Nat) := sourceZfrFixed z ∨
 numericClosedSeparation z ∨ numericClosedReplacement z

theorem sourceZfrAxiom_closed {z : Nat} (h : sourceZfrAxiom z) : sourceBound 0 z := by
 rcases h with hf | hs | hr
 · exact sourceZfrFixed_closed hf
 · exact hs.1
 · exact hr.1

theorem numericAllPrefix_encode (n : Nat) (a : Formula) :
 numericAllPrefix n (encodeFormula a) = encodeFormula (allPrefix n a) := by
 induction n <;> simp_all [numericAllPrefix, allPrefix, encodeFormula]

theorem numericSeparationCode_encode (n : Nat) (p : Formula) :
 numericSeparationCode (encodeFormula p) n = encodeFormula (separationSchema n p) := by
 simp only [numericSeparationCode, sourceRename_encode, separationSchema]
 rw [show numericSeparation (encodeFormula (rename sepIndex p)) =
   encodeFormula (separationFormula (rename sepIndex p)) from rfl]
 exact numericAllPrefix_encode n _

theorem numericReplacementCode_encode (n : Nat) (p : Formula) :
 numericReplacementCode (encodeFormula p) n = encodeFormula (replacementSchema n p) := by
 simp only [numericReplacementCode, sourceRename_encode, replacementSchema]
 rw [show numericReplacement (encodeFormula (rename repAIndex p))
   (encodeFormula (rename repBIndex p)) (encodeFormula (rename repCIndex p)) =
   encodeFormula (replacementFormula (rename repAIndex p) (rename repBIndex p) (rename repCIndex p)) from rfl]
 exact numericAllPrefix_encode n _

theorem separationSchema_in_zfr (n : Nat) (p : Formula) (hp : Bound p (n+1)) :
 sourceZfrAxiom (encodeFormula (separationSchema n p)) := by
 apply Or.inr; apply Or.inl
 exact ⟨(sourceBound_encode _ _).mpr (separationSchema_closed n p hp),
  encodeFormula p,n,(sourceBound_encode _ _).mpr hp,(numericSeparationCode_encode n p).symm⟩

theorem replacementSchema_in_zfr (n : Nat) (p : Formula) (hp : Bound p (n+2)) :
 sourceZfrAxiom (encodeFormula (replacementSchema n p)) := by
 apply Or.inr; apply Or.inr
 exact ⟨(sourceBound_encode _ _).mpr (replacementSchema_closed n p hp),
  encodeFormula p,n,(sourceBound_encode _ _).mpr hp,(numericReplacementCode_encode n p).symm⟩

theorem coreContext_in_zfr : ∀ p, p ∈ coreContext → sourceZfrAxiom (encodeFormula p) := by
 intro p hp
 simp only [coreContext,List.mem_cons,List.not_mem_nil,or_false] at hp
 rcases hp with rfl | rfl | rfl | rfl | rfl <;>
  simp [sourceZfrAxiom,sourceZfrFixed,fixedRefl,fixedEqElem,fixedSym,fixedPair,fixedFoundation,
    zfrRefl,zfrEqElem,zfrSym,zfrPair,zfrFoundation]

def sourceTheoryProvable (A : Nat → Prop) (f : Nat) :=
 ∃ G p, (∀ a, sourceMember a G → A a) ∧ sourceFullDerives p (sourceSequent G f)

theorem ND.theoryProvable {Γ : Context} {a : Formula} {A : Nat → Prop}
 (hΓ : ∀ p, p ∈ Γ → A (encodeFormula p)) (h : ND (.seq Γ a)) :
 sourceTheoryProvable A (encodeFormula a) := by
 obtain ⟨p,hp⟩ := h.exact_numeric_derives
 refine ⟨encodeContext Γ,p,?_,hp⟩
 intro c hc
 simp only [sourceMember,encodeContext,decodeSourceList_encode,List.mem_map] at hc
 obtain ⟨a,ha,rfl⟩ := hc
 exact hΓ a ha

end ZFR
