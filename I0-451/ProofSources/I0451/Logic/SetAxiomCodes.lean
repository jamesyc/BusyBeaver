module
public import I0451.Logic.ParameterizedZF
public import Internal.Arith.Standard
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.CraigTrick

/-! Arithmetic codes for the parameterized separation and replacement
schemata. The constructors use Foundation's bound-variable substitution
and coded universal closure. -/
@[expose] public section
namespace I0451.Logic

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open ZF207.Internal.Arith
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def membershipCode (i j : V) : V := ^rel 2 1 (^#i ∷ ^#j ∷ 0)
noncomputable def equalityCode (i j : V) : V := ^rel 2 0 (^#i ∷ ^#j ∷ 0)

noncomputable def bv4 (n : V) : V := termBShiftVec ℒₛₑₜ n (bv3 n)

noncomputable def separationInstanceCode (n p : V) : V :=
  qqAlls (qqAll (qqExs (qqAll (Bootstrapping.iff ℒₛₑₜ (membershipCode 0 1)
    (membershipCode 0 2 ^⋏ subst ℒₛₑₜ (^#(0 : V) ∷ bv3 n) p))))) n

noncomputable def replacementInstanceCode (n p : V) : V :=
  let atXY := subst ℒₛₑₜ (^#(1 : V) ∷ ^#(0 : V) ∷ bv2 n) p
  let atXZ := subst ℒₛₑₜ (^#(2 : V) ∷ ^#(0 : V) ∷ bv3 n) p
  let inRange := subst ℒₛₑₜ (^#(0 : V) ∷ ^#(1 : V) ∷ bv4 n) p
  let total := qqAll (qqExs (atXY ^⋏ qqAll (Bootstrapping.imp ℒₛₑₜ atXZ (equalityCode 0 1))))
  let image := qqAll (qqExs (qqAll (Bootstrapping.iff ℒₛₑₜ (membershipCode 0 1)
    (qqExs (membershipCode 0 3 ^⋏ inRange)))))
  qqAlls (Bootstrapping.imp ℒₛₑₜ total image) n

theorem separationInstanceCode_defined : 𝚺ᴬ₁-Function₂[V] (separationInstanceCode : V → V → V) := by
  unfold separationInstanceCode membershipCode
  definability

theorem replacementInstanceCode_defined : 𝚺ᴬ₁-Function₂[V] (replacementInstanceCode : V → V → V) := by
  unfold replacementInstanceCode membershipCode equalityCode bv4
  definability

private theorem bv4_semitermVec (n : V) : IsSemitermVec ℒₛₑₜ n (n + 4) (bv4 n) := by
  simpa [bv4, add_assoc, show (3 : V) + 1 = 4 by norm_num] using (bv3_semitermVec n).termBShiftVec

private theorem bv4_nth {i n : V} (hi : i < n) : (bv4 n).[i] = ^#(i + 4) := by
  simp [bv4, nth_termBShiftVec (bv3_semitermVec n).isUTerm hi, nth_bv3 hi, add_assoc,
    show (3 : V) + 1 = 4 by norm_num]

private theorem replacementArgs_quote {n d : Nat} (x y : Fin (n + d)) (vector : V)
    (length : len vector = (n : V)) (each : ∀ i < (n : V), vector.[i] = ^#(i + (d : V))) :
    SemitermVec.val (fun i => (⌜replacementArgs (ξ := Nat) x y i⌝ : Bootstrapping.Semiterm V ℒₛₑₜ (n + d))) =
      ^#((x : Nat) : V) ∷ ^#((y : Nat) : V) ∷ vector := by
  rw [SemitermVec.val_succ, SemitermVec.val_succ]
  have tail : (Matrix.vecTail (Matrix.vecTail fun i =>
      (⌜replacementArgs (ξ := Nat) x y i⌝ : Bootstrapping.Semiterm V ℒₛₑₜ (n + d)))) =
      fun j : Fin n => (⌜(#(j.addNat d) : SyntacticSemiterm ℒₛₑₜ (n + d))⌝ :
        Bootstrapping.Semiterm V ℒₛₑₜ (n + d)) := by
    funext j
    simp [Matrix.vecTail, replacementArgs]
  rw [tail, vec_bvars_eq vector length each]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_def]
  have firstTerm : replacementArgs (ξ := Nat) x y 0 = #x := by simp [replacementArgs]
  have secondTerm : replacementArgs (ξ := Nat) x y (Fin.succ 0) = #y := rfl
  rw [firstTerm, secondTerm]
  simp

private theorem quote_subst_parameters {n d : Nat} (φ : SetTheorySemisentence (n + 2))
    (x y : Fin (n + d)) (vec : V) (lenEq : len vec = (n : V))
    (each : ∀ i < (n : V), vec.[i] = ^#(i + (d : V))) :
    (⌜tpl φ (replacementArgs x y)⌝ : V) =
      subst ℒₛₑₜ (^#((x : Nat) : V) ∷ ^#((y : Nat) : V) ∷ vec) (⌜φ⌝ : V) := by
  rw [quote_tpl, replacementArgs_quote x y vec lenEq each, tq_eq]

private theorem quote_closeParameters {n : Nat} (φ : SetTheorySemisentence n) :
    (⌜(∀¹* φ : SetTheorySentence)⌝ : V) = qqAlls (⌜φ⌝ : V) (n : V) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (∀¹* φ : SetTheorySentence) = ∀¹* (∀¹ φ) from rfl]
    simpa [qqAlls_all] using ih (∀¹ φ)

private theorem quote_sentenceNeg {n : Nat} (φ : SetTheorySemisentence n) :
    (⌜∼φ⌝ : V) = Bootstrapping.neg ℒₛₑₜ (⌜φ⌝ : V) := by
  simp [Sentence.quote_def, quote_neg']

private theorem quote_boundParameters {n d : Nat}
    (φ : SetTheorySemisentence (n + 2)) (x y : Fin (n + d)) (vec : V)
    (lenEq : len vec = (n : V)) (each : ∀ i < (n : V), vec.[i] = ^#(i + (d : V))) :
    (⌜(φ ⇜ (replacementArgs x y))⌝ : V) =
      subst ℒₛₑₜ (^#((x : Nat) : V) ∷ ^#((y : Nat) : V) ∷ vec) (⌜φ⌝ : V) := by
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe]
  have same : (fun i => (Rew.emb (replacementArgs (ξ := Empty) x y i) : SyntacticSemiterm ℒₛₑₜ (n+d))) =
      replacementArgs x y := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases <;> rfl
  rw [same]
  exact quote_subst_parameters φ x y vec lenEq each

private theorem quote_membership {n : Nat} (i j : Fin n) :
    (⌜membershipAtom i j⌝ : V) = membershipCode (i.val : V) (j.val : V) := by
  simp [membershipAtom, membershipCode, Sentence.quote_def, Semiformula.coe_rel,
    Semiformula.quote_rel, SemitermVec.val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp_def]
  change ((Encodable.encode Language.Set.Rel.mem : Nat) : V) = 1
  rw [show Encodable.encode Language.Set.Rel.mem = 1 from rfl, Nat.cast_one]

private theorem quote_equality {n : Nat} (i j : Fin n) :
    (⌜equalityAtom i j⌝ : V) = equalityCode (i.val : V) (j.val : V) := by
  simp [equalityAtom, equalityCode, Sentence.quote_def, Semiformula.coe_rel,
    Semiformula.quote_rel, SemitermVec.val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp_def]
  rfl

private theorem quote_separationArgs {n : Nat} (φ : SetTheorySemisentence (n + 1)) :
    (⌜φ ⇜ separationArgs⌝ : V) = subst ℒₛₑₜ (^#(0 : V) ∷ bv3 (n : V)) (⌜φ⌝ : V) := by
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe]
  have same : (fun i => (Rew.emb (separationArgs i) : SyntacticSemiterm ℒₛₑₜ (n+3))) =
      pushV 3 0 := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [same]
  simpa only [Fin.val_zero, Nat.cast_zero, ← Sentence.quote_def] using
    (quote_subst_pushV3 (V := V) (φ : Semiproposition ℒₛₑₜ (n + 1)) 0)

theorem quote_separationInstance {n : Nat} (φ : SetTheorySemisentence (n + 1)) :
    (⌜(∀¹* separationWithParameters φ : SetTheorySentence)⌝ : V) =
      separationInstanceCode (n : V) (⌜φ⌝ : V) := by
  rw [quote_closeParameters]
  congr 1
  simp only [separationWithParameters, Semiformula.iff_eq, Sentence.quote_and, Sentence.quote_or,
    Sentence.quote_all, Sentence.quote_ex, quote_sentenceNeg, quote_membership, quote_separationArgs,
    Bootstrapping.iff, Bootstrapping.imp]
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt (show 1 < n + 2 by omega),
    Nat.mod_eq_of_lt (show 1 < n + 3 by omega), Nat.mod_eq_of_lt (show 2 < n + 3 by omega),
    Nat.mod_eq_of_lt (show 1 < n + 4 by omega), Nat.mod_eq_of_lt (show 3 < n + 4 by omega)]

theorem quote_replacementInstance {n : Nat} (φ : SetTheorySemisentence (n + 2)) :
    (⌜(∀¹* replacementWithParameters φ : SetTheorySentence)⌝ : V) =
      replacementInstanceCode (n : V) (⌜φ⌝ : V) := by
  rw [quote_closeParameters]
  congr 1
  have atXY := quote_boundParameters (V := V) φ (d := 2) 1 0 (bv2 (n : V)) (len_bv2 _) fun _ h => by
    simpa only [Nat.cast_ofNat] using nth_bv2 h
  have atXZ := quote_boundParameters (V := V) φ (d := 3) 2 0 (bv3 (n : V)) (len_bv3 _) fun _ h => by
    simpa only [Nat.cast_ofNat] using nth_bv3 h
  have inRange := quote_boundParameters (V := V) φ (d := 4) 0 1 (bv4 (n : V))
    (bv4_semitermVec _).lh fun _ h => by simpa only [Nat.cast_ofNat] using bv4_nth h
  simp only [replacementWithParameters, Semiformula.iff_eq, Semiformula.imp_eq, Sentence.quote_and,
    Sentence.quote_or, Sentence.quote_all, Sentence.quote_ex, quote_sentenceNeg,
    quote_membership, quote_equality, atXY, atXZ, inRange, Bootstrapping.imp, Bootstrapping.iff]
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt (show 1 < n + 2 by omega),
    Nat.mod_eq_of_lt (show 1 < n + 3 by omega), Nat.mod_eq_of_lt (show 2 < n + 3 by omega),
    Nat.mod_eq_of_lt (show 1 < n + 4 by omega), Nat.mod_eq_of_lt (show 3 < n + 4 by omega)]

private theorem formulaCode_closed {n raw : Nat} (valid : IsSemiformula ℒₛₑₜ n raw)
    (closed : shift ℒₛₑₜ raw = raw) :
    ∃ φ : SetTheorySemisentence n, (⌜φ⌝ : Nat) = raw := by
  obtain ⟨φ, rfl⟩ := valid.sound
  have fixed : Rewriting.shift φ = φ := (Semiformula.quote_inj_iff (V := Nat)).mp (by
    rw [Semiformula.quote_shift]
    exact closed)
  exact ⟨φ.toEmpty (Semiformula.freeVariables_eq_empty_of_shift_eq fixed),
    by rw [Sentence.quote_def, Semiformula.emb_toEmpty]⟩

private theorem finiteParameterSchema_re (arity : Nat)
    (schema : ∀ n : Nat, SetTheorySemisentence (n + arity) → SetTheorySentence)
    (compile : Nat → Nat → Nat) (graph : 𝚺ᴬ₁-Function₂ compile)
    (quotes : ∀ n φ, (⌜schema n φ⌝ : Nat) = compile n (⌜φ⌝ : Nat)) :
    Theory.RE ({σ | ∃ n φ, σ = schema n φ} : SetTheory) := by
  let generated (p : Nat) : Prop :=
    ∃ n q, IsSemiformula ℒₛₑₜ (n + arity) q ∧ shift ℒₛₑₜ q = q ∧ p = compile n q
  have generation : 𝚺ᴬ₁-Predicate generated := by unfold generated; definability
  have re := (rePred_iff_sigma1.mpr generation).comp (Computable.encode (α := SetTheorySentence))
  refine ⟨re.of_eq fun σ => ?_⟩
  constructor
  · rintro ⟨n, q, valid, fixed, output⟩
    obtain ⟨φ, rfl⟩ := formulaCode_closed valid fixed
    refine ⟨n, φ, ?_⟩
    apply Encodable.encode_injective
    have lhs : (⌜σ⌝ : Nat) = Encodable.encode σ := by simpa using (Sentence.quote_eq_encode (V := Nat) σ)
    have rhs : (⌜schema n φ⌝ : Nat) = Encodable.encode (schema n φ) := by
      simpa using (Sentence.quote_eq_encode (V := Nat) (schema n φ))
    rw [← lhs, ← rhs, quotes]
    exact lhs.trans output
  · rintro ⟨n, φ, rfl⟩
    have fixed : shift ℒₛₑₜ (⌜φ⌝ : Nat) = ⌜φ⌝ := by
      rw [Sentence.quote_def, ← Semiformula.quote_shift]
      congr 1
      unfold Rewriting.emb Rewriting.shift
      rw [← TransitiveRewriting.comp_app]
      congr 2
      ext x <;> simp
    refine ⟨n, ⌜φ⌝, ?_, fixed, ?_⟩
    · simpa [Sentence.quote_def] using (Semiformula.quote_isSemiformula (V := Nat) (φ : Semiproposition ℒₛₑₜ (n + arity)))
    · have enc : (⌜schema n φ⌝ : Nat) = Encodable.encode (schema n φ) := by
        simpa using (Sentence.quote_eq_encode (V := Nat) (schema n φ))
      exact enc.symm.trans (quotes n φ)

instance : parameterizedSeparation.RE :=
  finiteParameterSchema_re 1 (fun _ φ => ∀¹* separationWithParameters φ)
    separationInstanceCode separationInstanceCode_defined (fun _ φ => by simpa only [natCast_nat] using (quote_separationInstance (V := Nat) φ))

instance : parameterizedReplacement.RE :=
  finiteParameterSchema_re 2 (fun _ φ => ∀¹* replacementWithParameters φ)
    replacementInstanceCode replacementInstanceCode_defined (fun _ φ => by simpa only [natCast_nat] using (quote_replacementInstance (V := Nat) φ))

private noncomputable instance finiteSetLanguage : Language.Finite ℒₛₑₜ where
  func := by
    letI : IsEmpty ((k : Nat) × (ℒₛₑₜ).Func k) := ⟨fun p => nomatch p.2⟩
    exact Fintype.ofFinite _
  rel := by
    let tag : ((k : Nat) × (ℒₛₑₜ).Rel k) → Bool := fun p =>
      match p with | ⟨_, .eq⟩ => false | ⟨_, .mem⟩ => true
    letI : Finite ((k : Nat) × (ℒₛₑₜ).Rel k) :=
      Finite.of_injective tag (by rintro ⟨_,a⟩ ⟨_,b⟩; cases a <;> cases b <;> simp [tag])
    exact Fintype.ofFinite _

private theorem basicSetTheory_finite : Set.Finite (𝗕𝗦𝗧 : SetTheory) := by
  let fixed : SetTheory :=
    { “∃ e, !isEmpty e”,
      “∀ x y, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y”,
      “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y”,
      “∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w”,
      “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x”,
      “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧ (∀ x ∈ I, ∀ x', !isSucc x' x → x' ∈ I)”,
      “∀ x, !isNonempty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y” }
  have finite : Set.Finite fixed := by simp [fixed]
  apply (Theory.EqAxiom.finite.union finite).subset
  intro σ member
  cases member <;> simp [fixed, *]

instance : parameterizedZF.RE :=
  ((Theory.RE.ofFinite basicSetTheory_finite).add (inferInstance : parameterizedSeparation.RE)).add
    (inferInstance : parameterizedReplacement.RE)

end I0451.Logic
