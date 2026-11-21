module
public import I0451.Logic.NativeEquality
public import I0451.Logic.NameParameters
public import I0451.Logic.FoundationSyntaxCheck

/-! The theory certified by the literal native proof calculus contains
ZF and the Berkeley cardinal axiom. This is the external step that
places the imported consistency theorem in the native calculus. -/
@[expose] public section
namespace I0451.Logic

open FFL FFL.Entailment FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.FirstOrder.Arithmetic
open I0451.Arithmetization I0451.Runtime I0451.Omega I0451.Logic.NamedFormula
open I0451.Logic.SetAssignments

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* nativeSetTheory]

private theorem native_holds (f : NamedFormula) (proof : NativeDerivable f.code) :
    ∀ s : Nat → V, f.eval s :=
  (closedSentence_models f).mp (models_of_provable inferInstance (f.closedSentence_provable proof))

private theorem native_container :
    ∀ a : V, ∃ d : V, a ∈ d ∧ ∀ x ∈ d,
      (∃ w ∈ d, ∀ y : V, y ⊆ x → y ∈ w) ∧ x ⊆ d := by
  intro a
  exact (container_eval (fun _ => a)).mp
    (native_holds (container 1 2 3) (container_provable (by decide) (by decide)) (fun _ => a))

private theorem native_extensionality :
    ∀ x y : V, (∀ z : V, z ∈ x ↔ z ∈ y) → x = y := by
  intro x y equivalent
  let env (i : Nat) : V := if i = 1 then x else y
  have law := native_holds (NamedFormula.extensionality 1 2 3)
    (extensionality_provable (by decide) (by decide)) env
  exact (extensionality_eval env).mp law (fun z => (equivalent z).mp) (fun z => (equivalent z).mpr)

private theorem native_collection (R : V → V → Prop) (defR : ℒₛₑₜ-relation R) (A : V) :
    ∃ B : V, (∀ x ∈ A, (∃ y, R x y) → ∃ z ∈ B, R x z) ∧
      ∀ y ∈ B, ∃ x, R x y := by
  obtain ⟨f,s,fromSet,codeBig,related⟩ := name_definable_relation R defR A
  have ca : f.code ≠ 1 := by omega
  have cb : f.code ≠ 2 := by omega
  have cover := (collection_eval s f ca cb (fun h => (_root_.lt_irrefl _ (label_lt_code h)).elim)).mp
    (native_holds (collection 1 2 f) (collection_provable f ca cb) s)
  simpa only [fromSet, related] using cover

private theorem sentinel_normalizes (f : Formula) (ok : sentinelOnly f = true)
    (scope : List Nat) (pos : Bool) (free bound : Nat → V) :
    (f.normalize scope pos).eval (fun x y : V => x ∈ y) free bound ↔
      signed pos ((fromNative f).eval (namedEnvironment scope free bound)) := by
  induction f generalizing scope pos bound with
  | truth => cases pos <;> simp [Formula.normalize, fromNative, NamedFormula.eval, NormalForm.eval, signed]
  | equal a b => rfl
  | mem a b =>
    have allowed : a ≠ b ∨ a = 0 := of_decide_eq_true ok
    rcases allowed with differs | atZero
    · have read : fromNative (.mem a b) = .mem a b := by
        cases a <;> cases b <;> simp_all [fromNative]
      rw [read]
      simp [Formula.normalize, NormalForm.eval, NamedFormula.eval, differs, namedEnvironment]
    · subst a
      cases b with
      | zero => cases pos <;> simp [Formula.normalize, NormalForm.eval, fromNative, NamedFormula.eval, signed]
      | succ b => simp [Formula.normalize, NormalForm.eval, fromNative, NamedFormula.eval, namedEnvironment]
  | imp p q hp hq =>
    obtain ⟨op,oq⟩ := Bool.and_eq_true_iff.mp ok
    cases pos <;>
      simp only [Formula.normalize, Bool.false_eq_true, ite_false, ite_true, NormalForm.eval_joinAnd,
        NormalForm.eval_joinOr, hp op, hq oq, fromNative, NamedFormula.eval, signed] <;>
      apply Classical.byCases (p := (fromNative p).eval (namedEnvironment scope free bound)) <;>
      intro h <;> simp [h]
  | all label p ih =>
    cases pos
    · simp only [Formula.normalize, NormalForm.eval, fromNative, NamedFormula.eval, signed,
        Bool.false_eq_true, ite_false, Classical.not_forall]
      exact exists_congr fun v => by rw [ih ok, namedEnvironment_cons]; rfl
    · simp only [Formula.normalize, NormalForm.eval, fromNative, NamedFormula.eval, signed, ite_true]
      exact forall_congr' fun v => by rw [ih ok, namedEnvironment_cons]; rfl

private theorem source_foundation_named :
    fromNative SetSentences.foundationFormula =
      .all 0 (.imp (existsAt 1 (.mem 1 0))
        (existsAt 1 ((.mem 1 0 : NamedFormula).and
          (.all 2 (.imp (.mem 2 1) ((.mem 2 0 : NamedFormula).not)))))) := rfl

attribute [local irreducible] NamedFormula.existsAt NamedFormula.and NamedFormula.not

private theorem source_foundation_spec (s : Nat → V) :
    (fromNative SetSentences.foundationFormula).eval s ↔ SetSentences.Foundation (fun x y : V => x ∈ y) := by
  rw [source_foundation_named]
  simp only [NamedFormula.eval, NamedFormula.eval_existsAt, NamedFormula.eval_and, NamedFormula.eval_not,
    membership_rel, I0451.Logic.assign, ite_true, ite_false, SetSentences.Foundation]
  simp

private theorem checked_output {output : CounterExpr} {spec : Formula}
    (certified : matchesFormula output spec = true) :
    ∃ body, output.toFormula = some body ∧
      body.normalize [] true = spec.normalize [] true := by
  cases code : output.toFormula with
  | none => simp [matchesFormula,code] at certified
  | some body => exact ⟨body, rfl, by simpa [matchesFormula,code] using certified⟩

attribute [local irreducible] literalFoundationTerm literalBerkeleyTerm literalFoundationCode literalBerkeleyCode

set_option maxHeartbeats 700000 in
private theorem native_foundation : SetSentences.Foundation (fun x y : V => x ∈ y) := by
  obtain ⟨body, emitted, same⟩ := checked_output actual_foundation_checked
  have only : sentinelOnly body = true := by simpa only [emitted, Option.any_some] using literal_foundation_sentinel
  have isLiteral : literalFoundationCode = body.code :=
    literalFoundationCode_eq.trans (literalFoundationTerm.toFormula_sound (fun _ => 0) body emitted)
  have nativeProof : NativeDerivable (fromNative body).code := by
    rw [fromNative_code, ← isLiteral]
    simpa only [natCast_nat] using (NativeDerivable.foundation (V := Nat))
  let s : Nat → V := fun _ => Classical.arbitrary V
  have compiled := native_holds (fromNative body) nativeProof s
  have before := sentinel_normalizes (V := V) body only [] true s s
  have after := sentinel_normalizes (V := V) SetSentences.foundationFormula (by decide) [] true s s
  rw [same] at before
  have correct := after.mp (before.mpr compiled)
  exact (source_foundation_spec s).mp correct

theorem nativeSet_models_zf : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  SourceSetModel.models_zf ⟨native_foundation, native_extensionality, native_container, native_collection⟩

instance nativeSet_extends_zf : 𝗭𝗙 ⪯ nativeSetTheory :=
  Entailment.WeakerThan.ofAxm! fun h =>
    SetTheory.complete.{0} nativeSetTheory _ fun M _ _ _ => (nativeSet_models_zf (V := M)).models_set h

set_option maxHeartbeats 1500000 in
theorem nativeSet_berkeley : nativeSetTheory ⊢ berkeleySetAxiom := by
  apply SetTheory.complete.{0}
  intro W _ _ _
  let : W↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := nativeSet_models_zf
  obtain ⟨body, emitted, _⟩ := checked_output actual_berkeley_checked
  have isLiteral : literalBerkeleyCode = body.code :=
    literalBerkeleyCode_eq.trans (literalBerkeleyTerm.toFormula_sound (fun _ => 0) body emitted)
  have nativeProof : NativeDerivable (fromNative body).code := by
    rw [fromNative_code, ← isLiteral]
    simpa only [natCast_nat] using (NativeDerivable.berkeley (V := Nat))
  let s : Nat → W := fun _ => ∅
  have bodyTrue := native_holds (fromNative body) nativeProof s
  have syntactic := (fromNative_eval body s (fun _ => mem_irrefl _)).mp bodyTrue
  have literalTrue : Eval (fun x y : W => x ∈ y) s literalBerkeleyCode := by
    rw [isLiteral]
    exact (eval_formula (fun x y : W => x ∈ y) body s).mpr syntactic
  have verified := (Runtime.literal_berkeley_eval
    (E := fun x y : W => x ∈ y) (fun x : W => mem_irrefl x) s).mp literalTrue
  exact berkeleySetAxiom_models.mpr (compressed_yields_berkeley verified)

instance nativeSet_extends_berkeley : berkeleyTheory ⪯ nativeSetTheory :=
  Entailment.WeakerThan.ofAxm! fun h => by
    rcases h with zf | same
    · exact Entailment.WeakerThan.pbl (Entailment.by_axm zf : 𝗭𝗙 ⊢ _)
    · have eq : _ = berkeleySetAxiom := same
      rw [eq]
      exact nativeSet_berkeley

end I0451.Logic
