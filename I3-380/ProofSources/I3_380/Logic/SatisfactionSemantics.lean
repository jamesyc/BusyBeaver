module
public import I3_380.Logic.I3
public import I3_380.Logic.RankSemantics
@[expose] public section

namespace PalomarI3380.Logic.Internal

variable {V : Type} (E : V → V → Prop)

def FunctionInto (graph domain range : V) : Prop :=
  FunctionOn E graph domain ∧ ∀ x, E x domain → ∀ y, At E graph x y → E y range

def RowAt (rows i tag first second : V) : Prop :=
  ∃ row operands, At E rows i row ∧ OrderedPair E tag operands row ∧ OrderedPair E first second operands

def ValidRow (arity i tag first second : V) : Prop :=
  (Numeral E 0 tag ∧ E first arity ∧ E second arity) ∨
  (Numeral E 1 tag ∧ E first arity ∧ E second arity) ∨
  (Numeral E 2 tag ∧ E first i) ∨
  (Numeral E 3 tag ∧ E first i ∧ E second i) ∨
  (Numeral E 4 tag ∧ E first arity ∧ E second i)

def SyntaxCode (w arity count rows : V) : Prop :=
  E arity w ∧ E count w ∧ ¬Empty E count ∧ FunctionOn E rows count ∧
    ∀ i, E i count → ∃ tag first second, RowAt E rows i tag first second ∧
      E first w ∧ E second w ∧ ValidRow E arity i tag first second

def AgreesAway (arity a b index : V) : Prop :=
  ∀ i, E i arity → i ≠ index → ∀ x, At E a i x ↔ At E b i x

def AtomicTruth (R : V → V → Prop) (env first second : V) : Prop :=
  ∃ x y, At E env first x ∧ At E env second y ∧ R x y

def RowTruth (truth : V → V → Prop) (arity stage env tag first second : V) : Prop :=
  (Numeral E 0 tag ∧ AtomicTruth E Eq env first second) ∨
  (Numeral E 1 tag ∧ AtomicTruth E E env first second) ∨
  (Numeral E 2 tag ∧ ¬truth first env) ∨
  (Numeral E 3 tag ∧ truth first env ∧ truth second env) ∨
  (Numeral E 4 tag ∧ ∃ amended, FunctionInto E amended arity stage ∧
     AgreesAway E arity env amended first ∧ truth second amended)

def TruthSet (arity count rows stage sat : V) : Prop :=
  ∀ i, E i count → ∀ env, FunctionInto E env arity stage →
    ∃ tag first second, RowAt E rows i tag first second ∧
      (At E sat i env ↔ RowTruth E (At E sat) arity stage env tag first second)

def MappedAssignment (arity embedding source target : V) : Prop :=
  ∀ i, E i arity → ∀ x y, At E source i x → At E embedding x y → At E target i y

def ElementaryOnRank (w stage embedding : V) : Prop :=
  ∀ arity count rows, SyntaxCode E w arity count rows →
    ∃ sat, TruthSet E arity count rows stage sat ∧
      ∀ i, E i count → ∀ source target,
        FunctionInto E source arity stage → FunctionInto E target arity stage →
        MappedAssignment E arity embedding source target →
        (At E sat i source ↔ At E sat i target)

def HasI3 : Prop :=
  ∃ w height stage embedding, Omega E w ∧ RankLike E height stage ∧ Inductive E height ∧
    FunctionInto E embedding stage stage ∧
    (∃ x y, E x stage ∧ E y stage ∧ At E embedding x y ∧ x ≠ y) ∧
    ElementaryOnRank E w stage embedding

end PalomarI3380.Logic.Internal

namespace PalomarI3380.Logic.SetFormula

variable {V : Type} {E : V → V → Prop} {d : Nat} {env : Nat → V} {default : V}

theorem holds_functionInto {f a b : Nat} (hf : f < d) (ha : a < d) (hb : b < d) :
    holds E (functionInto f a b) d env default ↔ Internal.FunctionInto E (env f) (env a) (env b) := by
  simp (disch := omega) only [functionInto, holds_both, holds_functionOn, holds_eachIn, holds_every,
    holds_implies, holds_graphValue, holds_mem, assign_earlier, assign_here, Internal.FunctionInto]

theorem holds_validRow {a i t x y : Nat} (ha : a < d) (hi : i < d) (ht : t < d) (hx : x < d) (hy : y < d) :
    holds E (validRow a i t x y) d env default ↔ Internal.ValidRow E (env a) (env i) (env t) (env x) (env y) := by
  simp (disch := assumption) only [validRow, anyOf, allOf, holds_either, holds_both, holds_falsity, or_false,
    holds_neg, not_false_eq_true, and_true, holds_numeral, holds_mem, Internal.ValidRow]

theorem holds_syntaxCode {w a c r : Nat} (hw : w < d) (ha : a < d) (hc : c < d) (hr : r < d) :
    holds E (syntaxCode w a c r) d env default ↔ Internal.SyntaxCode E (env w) (env a) (env c) (env r) := by
  simp (disch := omega) only [syntaxCode, syntaxRow, allOf, holds_both, holds_mem, holds_neg,
    holds_empty, holds_functionOn, holds_eachIn, holds_someSet, holds_graphValue, holds_orderedPair,
    holds_validRow, assign_here, assign_earlier, holds_falsity, not_false_eq_true, and_true, Internal.SyntaxCode]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _
  constructor
  · rintro ⟨row, tag, operands, a, b, rowAt, tagPair, argsPair, rest⟩
    exact ⟨tag, a, b, ⟨row, operands, rowAt, tagPair, argsPair⟩, rest⟩
  · rintro ⟨tag, a, b, ⟨row, operands, rowAt, tagPair, argsPair⟩, rest⟩
    exact ⟨row, tag, operands, a, b, rowAt, tagPair, argsPair, rest⟩

theorem holds_agreesAway {a f g i : Nat} (ha : a < d) (hf : f < d) (hg : g < d) (hi : i < d) :
    holds E (agreesAway a f g i) d env default ↔ Internal.AgreesAway E (env a) (env f) (env g) (env i) := by
  simp (disch := omega) only [agreesAway, holds_eachIn, holds_implies, holds_neg, holds_eq, holds_every,
    holds_iff, holds_graphValue, assign_here, assign_earlier, Internal.AgreesAway]

theorem holds_atomicEquality {a x y : Nat} (ha : a < d) (hx : x < d) (hy : y < d) :
    holds E (atomicTruth eq a x y) d env default ↔ Internal.AtomicTruth E Eq (env a) (env x) (env y) := by
  simp (disch := omega) only [atomicTruth, holds_someSet, allOf, holds_both, holds_graphValue,
    holds_eq, holds_neg, holds_falsity, not_false_eq_true, and_true, assign_here, assign_earlier,
    Internal.AtomicTruth]

theorem holds_atomicMembership {a x y : Nat} (ha : a < d) (hx : x < d) (hy : y < d) :
    holds E (atomicTruth mem a x y) d env default ↔ Internal.AtomicTruth E E (env a) (env x) (env y) := by
  simp (disch := omega) only [atomicTruth, holds_someSet, allOf, holds_both, holds_graphValue,
    holds_mem, holds_neg, holds_falsity, not_false_eq_true, and_true, assign_here, assign_earlier,
    Internal.AtomicTruth]

theorem holds_rowTruth {a s t v g x y : Nat} (ha : a < d) (hs : s < d) (ht : t < d) (hv : v < d)
    (hg : g < d) (hx : x < d) (hy : y < d) :
    holds E (rowTruth a s t v g x y) d env default ↔
      Internal.RowTruth E (Internal.At E (env t)) (env a) (env s) (env v) (env g) (env x) (env y) := by
  simp (disch := omega) only [rowTruth, anyOf, allOf, holds_either, holds_both, holds_numeral,
    holds_atomicEquality, holds_atomicMembership, holds_neg, holds_falsity, not_false_eq_true,
    or_false, and_true, holds_graphValue, holds_someSet, holds_functionInto, holds_agreesAway,
    assign_here, assign_earlier, Internal.RowTruth]

theorem holds_truthSet {a c r s t : Nat} (ha : a < d) (hc : c < d) (hr : r < d) (hs : s < d) (ht : t < d) :
    holds E (truthSet a c r s t) d env default ↔ Internal.TruthSet E (env a) (env c) (env r) (env s) (env t) := by
  simp (disch := omega) only [truthSet, syntaxRow, allOf, holds_both, holds_eachIn, holds_every, holds_implies,
    holds_functionInto, holds_someSet, holds_graphValue, holds_orderedPair, holds_iff, holds_rowTruth,
    holds_neg, holds_falsity, not_false_eq_true, and_true, assign_here, assign_earlier, Internal.TruthSet]
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro e
  apply imp_congr_right
  intro _
  constructor
  · rintro ⟨r, t, operands, a, b, hR, hT, hAB, rest⟩
    exact ⟨t, a, b, ⟨r, operands, hR, hT, hAB⟩, rest⟩
  · rintro ⟨t, a, b, ⟨r, operands, hR, hT, hAB⟩, rest⟩
    exact ⟨r, t, operands, a, b, hR, hT, hAB, rest⟩

theorem holds_mappedAssignment {a j s t : Nat} (ha : a < d) (hj : j < d) (hs : s < d) (ht : t < d) :
    holds E (mappedAssignment a j s t) d env default ↔ Internal.MappedAssignment E (env a) (env j) (env s) (env t) := by
  simp (disch := omega) only [mappedAssignment, holds_eachIn, holds_every, holds_implies, holds_both,
    holds_graphValue, assign_here, assign_earlier, Internal.MappedAssignment, and_imp]

theorem holds_elementaryOnRank {w r j : Nat} (hw : w < d) (hr : r < d) (hj : j < d) :
    holds E (elementaryOnRank w r j) d env default ↔ Internal.ElementaryOnRank E (env w) (env r) (env j) := by
  simp (disch := omega) only [elementaryOnRank, allOf, holds_every, holds_implies, holds_syntaxCode,
    holds_someSet, holds_both, holds_truthSet, holds_eachIn, holds_functionInto, holds_mappedAssignment,
    holds_iff, holds_graphValue, holds_neg, holds_falsity, not_false_eq_true, and_true, and_imp,
    assign_here, assign_earlier, Internal.ElementaryOnRank]

set_option maxHeartbeats 1500000 in
theorem holds_i3 :
    eval E i3Axiom env ↔ Internal.HasI3 E := by
  let body : SetFormula := someSet fun w => someSet fun height => someSet fun stage => someSet fun embedding =>
    allOf [omegaSet w, rank height stage, inductiveSet height, functionInto embedding stage stage,
      someIn stage fun x => someIn stage fun y => both (graphValue embedding x y) (neg (eq x y)),
      elementaryOnRank w stage embedding]
  have semantics : holds E body 0 env (env 0) ↔ Internal.HasI3 E := by
    simp (disch := omega) only [body, allOf, holds_someSet, holds_both, holds_omegaSet, holds_rank, holds_inductiveSet,
      holds_functionInto, holds_someIn, holds_graphValue, holds_neg, holds_eq, holds_elementaryOnRank,
      holds_falsity, not_false_eq_true, and_true, assign_here, assign_earlier, Internal.HasI3]
    constructor
    · rintro ⟨w, a, s, f, omega, rank, limit, funIn, ⟨x, hx, y, hy, value, ne⟩, elementarity⟩
      exact ⟨w, a, s, f, omega, rank, limit, funIn, ⟨x, y, hx, hy, value, ne⟩, elementarity⟩
    · rintro ⟨w, a, s, f, omega, rank, limit, funIn, ⟨x, y, hx, hy, value, ne⟩, elementarity⟩
      exact ⟨w, a, s, f, omega, rank, limit, funIn, ⟨x, hx, y, hy, value, ne⟩, elementarity⟩
  exact (eval_congr_bound i3Axiom i3_closed (t := assignment 0 env (env 0)) (fun i hi => by omega)).trans semantics

end PalomarI3380.Logic.SetFormula
