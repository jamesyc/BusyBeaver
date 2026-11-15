module
public import HeadSixTemplate
public import ExactGateSemantics
public import FormulaEquality
public import LogicalEquivalence
public import RankHullDiagonalLogic
public import NegativeEncodingEquivalence
@[expose] public section
namespace ZFR
open C209Soundness

/-- Literal named-syntax tree for the emitted gate. The opaque relation leaf
is A, while a also remains the gate's binder label. -/
def namedPointedGate (A : C209Soundness.Formula) (a d h : Nat) : C209Soundness.Formula :=
(.imp (.imp (.imp (.eq h d) (.all a (.eq h d))) (.imp (.imp (.mem h d) (.all a (.mem h d))) (.all a (.imp (.all h (.imp (.mem h a) (.imp (.all d (.imp A (.imp (.all d (.imp (.all a (.imp (.mem a d) (.mem a h))) (.all h (.imp A (.imp (.all h (.imp A (.imp (.mem h a) (.mem 0 0)))) (.mem 0 0)))))) (.mem 0 0)))) (.mem 0 0)))) (.imp (.imp A (.mem h a)) (.mem 0 0)))))) (.mem 0 0))

theorem impCode_pos_right (a b : Nat) (hb : 0 < b) : 0 < impCode a b := by
 have := cantor_ge_right a b
 unfold impCode
 omega

theorem decode_impCode_right (a b : Nat) (hb : 0 < b) :
 decodeNat (impCode a b) = C209Soundness.Formula.imp (decodeNat a) (decodeNat b) :=
 decode_impCode_pos a b (by change impCode a b ≠ 0; have := impCode_pos_right a b hb; omega)

theorem decode_memCode (a b : Nat) : decodeNat (memCode a b) = C209Soundness.Formula.mem a b := by
 rw [decodeNat]
 have hq : memCode a b / 4 = cantor a b := by unfold memCode; omega
 have ht : memCode a b % 4 = 1 := by unfold memCode; omega
 have hn : memCode a b ≠ 0 := by unfold memCode; omega
 simp [hn,hq,ht,unpair_cantor]

theorem decode_eqCode (a b : Nat) : decodeNat (eqCode a b) = C209Soundness.Formula.eq a b := by
 rw [decodeNat]
 have hq : eqCode a b / 4 = cantor a b := by unfold eqCode; omega
 have ht : eqCode a b % 4 = 3 := by unfold eqCode; omega
 have hn : eqCode a b ≠ 0 := by unfold eqCode; omega
 simp [hn,hq,ht,unpair_cantor]

theorem decode_one : decodeNat 1 = C209Soundness.Formula.mem 0 0 := decode_memCode 0 0

theorem memCode_pos (a b : Nat) : 0 < memCode a b := by unfold memCode; omega
theorem eqCode_pos (a b : Nat) : 0 < eqCode a b := by unfold eqCode; omega
theorem allCode_pos (a b : Nat) : 0 < allCode a b := by unfold allCode; omega

theorem decode_allCode_exact (i a : Nat) :
 decodeNat (allCode i a) = C209Soundness.Formula.all i (decodeNat a) := decode_allCode a i

theorem decode_pointedGate_exact (a d h : Nat) :
 decodeNat (pointedGateCode a d h) = namedPointedGate (decodeNat a) a d h := by
 simp only [pointedGateCode, namedPointedGate, decode_impCode_right, decode_allCode_exact,
   decode_memCode, decode_eqCode, decode_one, impCode_pos_right,
   memCode_pos, eqCode_pos, allCode_pos, Nat.zero_lt_succ]

/-- Exact syntactic normalization, not merely semantic equivalence. -/
theorem translate_pointedGate_exact (ρ : Nat → Nat) (a d h : Nat) :
 translateCode ρ (pointedGateCode a d h) = translate ρ (namedPointedGate (decodeNat a) a d h) := by
 unfold translateCode
 rw [decode_pointedGate_exact]


theorem translate_labels_agree (p : C209Soundness.Formula) (n : Nat)
 (hp : p.LabelsLT n) (ρ τ : Nat → Nat) (h : ∀ i, i<n → ρ i = τ i) :
 translate ρ p = translate τ p := by
 induction p generalizing ρ τ with
 | truth => rfl
 | mem i j => simp only [translate,h i hp.1,h j hp.2]
 | eq i j => simp only [translate,h i hp.1,h j hp.2]
 | imp p q ihp ihq => simp only [translate,ihp hp.1 ρ τ h,ihq hp.2 ρ τ h]
 | all i p ih =>
   simp only [translate]
   congr 1
   apply ih hp.2
   intro j hj
   by_cases he : j=i <;> simp [bindName,he,h j hj]

theorem decodeNat_labels (a : Nat) : (decodeNat a).LabelsLT a := by
 simpa only [decodeNat_code] using (decodeNat a).labels_below_code

/-- The relation's own numeric code is a fresh variable label, syntactically. -/
theorem translateCode_self_binder (a : Nat) (ρ : Nat → Nat) :
 translateCode (bindName a ρ) a = shift (translateCode ρ a) := by
 unfold shift translateCode
 rw [rename_translate]
 apply translate_labels_agree (decodeNat a) a (decodeNat_labels a)
 intro i hi
 have hia : i ≠ a := by omega
 simp [bindName,hia]

/-- Construction tree distinguishes the arbitrary relation leaf from emitted
false surrogates; false occurrences inside the relation are never rewritten. -/
inductive GateTree where
 | relation
 | falsum
 | mem : Nat → Nat → GateTree
 | eq : Nat → Nat → GateTree
 | imp : GateTree → GateTree → GateTree
 | all : Nat → GateTree → GateTree

def GateTree.toSource (A : C209Soundness.Formula) (falseAt : (Nat → Nat) → Formula)
 (ρ : Nat → Nat) : GateTree → Formula
 | .relation => translate ρ A
 | .falsum => falseAt ρ
 | .mem i j => .mem (ρ i) (ρ j)
 | .eq i j => .eq (ρ i) (ρ j)
 | .imp p q => .imp (p.toSource A falseAt ρ) (q.toSource A falseAt ρ)
 | .all i p => .all (p.toSource A falseAt (bindName i ρ))

def realGateFalse (ρ : Nat → Nat) : Formula := .mem (ρ 0) (ρ 0)
def botGateFalse (_ρ : Nat → Nat) : Formula := .bot

theorem GateTree.false_equiv (t : GateTree) (A : C209Soundness.Formula)
 {Γ : Context} (hc : ContextSub coreContext Γ) (ρ : Nat → Nat) :
 NDEquiv Γ (t.toSource A realGateFalse ρ) (t.toSource A botGateFalse ρ) := by
 induction t generalizing Γ ρ with
 | relation => exact NDEquiv.refl _ _
 | falsum => exact core_false_surrogate hc (ρ 0)
 | mem => exact NDEquiv.refl _ _
 | eq => exact NDEquiv.refl _ _
 | imp p q ihp ihq => exact (ihp hc ρ).imp (ihq hc ρ)
 | all i p ih => exact (ih (core_subset_shift hc) (bindName i ρ)).all

def pointedGateTree (a d h : Nat) : GateTree :=
(.imp (.imp (.imp (.eq h d) (.all a (.eq h d))) (.imp (.imp (.mem h d) (.all a (.mem h d))) (.all a (.imp (.all h (.imp (.mem h a) (.imp (.all d (.imp .relation (.imp (.all d (.imp (.all a (.imp (.mem a d) (.mem a h))) (.all h (.imp .relation (.imp (.all h (.imp .relation (.imp (.mem h a) .falsum))) .falsum))))) .falsum))) .falsum))) (.imp (.imp .relation (.mem h a)) .falsum))))) .falsum)

def botPointedGate (a d h : Nat) (ρ : Nat → Nat) : Formula :=
 (pointedGateTree a d h).toSource (decodeNat a) botGateFalse ρ

theorem pointedGateTree_real (a d h : Nat) (ρ : Nat → Nat) :
 (pointedGateTree a d h).toSource (decodeNat a) realGateFalse ρ =
 translateCode ρ (pointedGateCode a d h) := by
 rw [translate_pointedGate_exact]
 rfl

/-- Actual ND equivalence replaces only the emitted false surrogates,
using the concrete Foundation derivation throughout shifted contexts. -/
theorem pointedGate_false_equiv (a d h : Nat) (ρ : Nat → Nat)
 {Γ : Context} (hc : ContextSub coreContext Γ) :
 NDEquiv Γ (translateCode ρ (pointedGateCode a d h)) (botPointedGate a d h ρ) := by
 rw [← pointedGateTree_real]
 exact (pointedGateTree a d h).false_equiv (decodeNat a) hc ρ


def rawDiagonalBody (psi : Formula) : Formula := .all (.imp (.mem 0 1)
 (.imp (.all (.imp (bumpPredicate psi)
   (.imp (.all (.imp (.all (.imp (.mem 0 1) (.mem 0 1)))
     (.all (.imp (bumpN 3 psi)
       (.imp (.all (.imp (bumpN 4 psi) (.imp (.mem 0 5) .bot))) .bot))))) .bot))) .bot))

def vacuousAll (p : Formula) : Formula := .imp p (.all (shift p))

theorem translate_shadow (p : C209Soundness.Formula) (x : Nat) (ρ : Nat → Nat) :
 translate (bindName x (bindName x ρ)) p = bumpPredicate (translate (bindName x ρ) p) := by
 unfold bumpPredicate
 rw [rename_translate]
 congr 1
 funext j
 by_cases h : j=x <;> simp [bindName,h,lift]

theorem relation_point_restore (p : C209Soundness.Formula) (x : Nat) :
 subst (x+1) (bumpPredicate (translate (bindName x id) p)) = shift (translate id p) := by
 simp only [subst,bumpPredicate,shift,rename_comp,rename_translate]
 congr 1
 funext j
 by_cases h : j=x
 · subst j; simp [bindName,lift,substMap]
 · simp [bindName,h,lift,substMap]

theorem translate_fresh_container (a : Nat) :
 translate (bindName a id) (decodeNat a) = shift (translate id (decodeNat a)) :=
 translateCode_self_binder a id

theorem translate_container_argument (a x : Nat) :
 translate (bindName x (bindName a id)) (decodeNat a) =
 bumpPredicate (translate (bindName x id) (decodeNat a)) := by
 unfold bumpPredicate
 rw [rename_translate]
 apply translate_labels_agree (decodeNat a) a (decodeNat_labels a)
 intro i hi
 have hia : i ≠ a := by omega
 by_cases hix : i=x <;> simp [bindName,hia,hix,lift]


def rawDiagonalUniversal (i : Nat) (phi : Formula) : Formula :=
 .all (.imp (rawDiagonalBody (bumpPredicate phi))
   (.imp (.imp (subst (i+1) (bumpPredicate phi)) (.mem (i+1) 0)) .bot))

theorem botPointedGate_diagonal_shape (a x : Nat) (hax : a ≠ x) :
 botPointedGate a x x id =
 .imp (.imp (vacuousAll (.eq x x)) (.imp (vacuousAll (.mem x x))
   (rawDiagonalUniversal x (translate (bindName x id) (decodeNat a))))) .bot := by
 simp only [botPointedGate,pointedGateTree,GateTree.toSource,botGateFalse,
   rawDiagonalUniversal,rawDiagonalBody,vacuousAll,translate_shadow,translate_container_argument,
   translate_fresh_container,relation_point_restore,bumpN]
 simp [bindName,hax,Ne.symm hax,shift,rename]


theorem ex_and_encoding_congr {Γ : Context} (p q q' : Formula)
 (hq : NDEquiv (shiftContext Γ) q q') :
 NDEquiv Γ (.ex (.and p q)) (.imp (.all (.imp p (.imp q' .bot))) .bot) := by
 apply (NDEquiv.ex_and_encoding Γ p q).trans
 apply NDEquiv.imp
 · apply NDEquiv.all
   exact (NDEquiv.refl _ p).imp (hq.imp (NDEquiv.refl _ .bot))
 · exact NDEquiv.refl _ .bot

theorem diagonalBody_raw_equiv (Γ : Context) (psi : Formula) :
 NDEquiv Γ (diagonalBody psi) (rawDiagonalBody psi) := by
 unfold diagonalBody rawDiagonalBody
 apply NDEquiv.all
 apply NDEquiv.imp (NDEquiv.refl _ _)
 apply ex_and_encoding_congr
 apply NDEquiv.all
 apply NDEquiv.imp (NDEquiv.refl _ _)
 apply NDEquiv.all
 apply NDEquiv.imp (NDEquiv.refl _ _)
 exact NDEquiv.ex_and_encoding _ _ _

/-- Positive diagonal witness implies exactly the raw negative outer gate. -/
theorem diagonalPointed_raw_equiv (Γ : Context) (i : Nat) (phi : Formula) :
 NDEquiv Γ (.ex (diagonalPointedBody i phi)) (.imp (rawDiagonalUniversal i phi) .bot) := by
 unfold diagonalPointedBody rawDiagonalUniversal
 apply (NDEquiv.ex_and_encoding Γ _ _).trans
 apply NDEquiv.imp
 · apply NDEquiv.all
   apply NDEquiv.imp (diagonalBody_raw_equiv _ _)
   exact NDEquiv.refl _ _
 · exact NDEquiv.refl _ _

theorem nd_vacuousAll (Γ : Context) (p : Formula) : ND (.seq Γ (vacuousAll p)) := by
 apply ND.ii
 apply ND.allI
 exact ND.ctx (by simp [shiftContext])

theorem nd_diagonal_raw_to_bot_gate (a x : Nat) (hax : a ≠ x) {Γ : Context}
 (h : ND (.seq Γ (.imp (rawDiagonalUniversal x (translate (bindName x id) (decodeNat a))) .bot))) :
 ND (.seq Γ (botPointedGate a x x id)) := by
 rw [botPointedGate_diagonal_shape a x hax]
 apply ND.ii
 apply ND.ie h.weaken_cons
 exact ND.ie (ND.ie (ND.ctx (by simp)) (nd_vacuousAll _ (.eq x x))) (nd_vacuousAll _ (.mem x x))

/-- Syntactic positive-to-literal diagonal gate bridge. No gate truth or
rank/hull assumption: only a provided positive witness proof and the
literal fixed axioms used to replace emitted false surrogates. -/
theorem nd_positive_to_literal_diagonal (a x : Nat) (hax : a ≠ x) {Γ : Context}
 (hc : ContextSub coreContext Γ)
 (h : ND (.seq Γ (.ex (diagonalPointedBody x (translate (bindName x id) (decodeNat a)))))) :
 ND (.seq Γ (translateCode id (pointedGateCode a x x))) := by
 have hraw := ND.ie (diagonalPointed_raw_equiv Γ x _).1 h
 have hbot := nd_diagonal_raw_to_bot_gate a x hax hraw
 exact ND.ie (pointedGate_false_equiv a x x id hc).2 hbot

end ZFR
