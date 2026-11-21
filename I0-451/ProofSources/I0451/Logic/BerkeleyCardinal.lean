module
public import I0451.Logic.BerkeleyOrdinals
public import I0451.Logic.ElementaryOrdinals

/-! The least proto-Berkeley ordinal is an uncountable initial ordinal.
Together with the cofinal critical-point argument this gives the
Berkeley cardinal asserted by the compressed sentence. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode I0451.Logic.ZFModel I0451.Logic.SetFormulaPrograms

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

theorem critical_not_natural {D code κ : V} (transitive : IsTransitive D)
    (elementaryCode : CodedElementary D code) (critical : CodedCriticalPoint D code κ) :
    κ ∉ (ω : V) := by
  intro natural
  obtain ⟨j, decoded, elementary⟩ := elementaryCode.decoded_elementary
  let k : Domain E D := ⟨κ, critical.1⟩
  have shapes := (cases_mem_succ_nat natural).2 κ (mem_succ_self κ)
  apply critical.2.1
  apply (decoded.at_iff k _).mpr
  rcases shapes with zero | ⟨p, before, successor⟩
  · have empty : k.val = ∅ := zero.trans zero_def
    exact (elementary_preserves_empty transitive elementary k empty).trans empty.symm
  · let predecessor : Domain E D := ⟨p, transitive.transitive κ critical.1 p before⟩
    have unchanged := (decoded.at_iff predecessor _).mp (critical.2.2 p before)
    have after := elementary_preserves_successor transitive elementary k predecessor successor
    rw [unchanged] at after
    exact after.trans successor.symm

theorem proto_uncountable {δ : Ordinal V} (proto : ProtoBerkeleyOrdinal δ.val) :
    (ω : V) ∈ (δ : V) := by
  let D := TransitiveClosure.transClosure ({δ.val} : V)
  have transitive : IsTransitive D := inferInstance
  have inside : δ.val ∈ D := TransitiveClosure.self_subset_transClosure δ.val (by simp)
  obtain ⟨code, κ, earlier, elementary, critical⟩ := proto.2 D transitive inside
  let κOrd := (IsOrdinal.of_mem earlier).toOrdinal
  let natOrd := (IsOrdinal.ω (V := V)).toOrdinal
  rcases lt_trichotomy natOrd κOrd with below | same | above
  · exact δ.ordinal.toIsTransitive.transitive κ earlier _ below
  · rw [show (ω : V) = κ from congrArg Ordinal.val same]
    exact earlier
  · exact (critical_not_natural transitive elementary critical above).elim

def InitialOrdinal (δ : V) : Prop :=
  IsOrdinal δ ∧ ∀ η ∈ δ, ¬∃ f, f ∈ δ ^ η ∧ range f = δ

private theorem proto_of_ordinal_surjection {δ η f : V} (proto : ProtoBerkeleyOrdinal δ)
    (earlier : η ∈ δ) (surjection : f ∈ δ ^ η) (rangeEq : range f = δ) :
    ProtoBerkeleyOrdinal η := by
  let : IsOrdinal δ := proto.1
  let ηOrd := (IsOrdinal.of_mem earlier).toOrdinal
  refine ⟨ηOrd.ordinal, fun M transitive ηM => ?_⟩
  obtain ⟨D,transD,mIn,fIn,dIn,keeps⟩ := coded_envelope_three M f δ
  obtain ⟨code,k,kBelow,elementaryCode,critical⟩ := proto.2 D transD dIn
  obtain ⟨fixedM,fixedF,_⟩ := keeps code elementaryCode
  have smaller : k ∈ η := by
    by_contra tooLarge
    let kOrd := (IsOrdinal.of_mem kBelow).toOrdinal
    have lower : ηOrd ≤ kOrd := le_of_not_gt (fun h : kOrd < ηOrd => tooLarge h)
    have inRange : k ∈ range f := rangeEq.symm ▸ kBelow
    obtain ⟨x, read⟩ := mem_range_iff.mp inRange
    have xEta := (mem_of_mem_functions surjection read).1
    have xK := lower x xEta
    have pairInD := transD.transitive f fIn _ read
    have xInD := (pair_components_in transD pairInD).1
    obtain ⟨j, decoded, elementary⟩ := elementaryCode.decoded_elementary
    let src : Domain E D := ⟨x,xInD⟩
    let target : Domain E D := ⟨k,critical.1⟩
    let table : Domain E D := ⟨f,fIn⟩
    let pair : Domain E D := ⟨⟨x,k⟩ₖ,pairInD⟩
    have srcFixed := (decoded.at_iff src _).mp (critical.2.2 x xK)
    have tableFixed : j table = table := Subtype.ext ((decoded.at_iff table _).mp fixedF)
    have transported := (elementary.mem_iff pair table).mp read
    rw [tableFixed] at transported
    have pairEq := elementary_preserves_kpair transD elementary (p := pair) (x := src) (y := target) rfl
    change (j pair).val ∈ f at transported
    rw [pairEq, srcFixed] at transported
    let : IsFunction f := IsFunction.of_mem surjection
    exact critical.2.1 ((decoded.at_iff target k).mpr (IsFunction.unique transported read))
  have inM := transitive.transitive η ηM k smaller
  obtain ⟨restricted, point⟩ := elementaryCode.restrict_critical transD transitive mIn fixedM critical inM
  exact ⟨restrictedGraph code M,k,smaller,restricted,point⟩

theorem least_proto_initial {δ : Ordinal V} (proto : ProtoBerkeleyOrdinal δ.val)
    (least : ∀ η : Ordinal V, ProtoBerkeleyOrdinal η.val → δ ≤ η) :
    InitialOrdinal δ.val := by
  refine ⟨δ.ordinal, fun η inside ⟨f, function, rangeEq⟩ => ?_⟩
  let ηOrd := (IsOrdinal.of_mem inside).toOrdinal
  have smallerProto := proto_of_ordinal_surjection proto inside function rangeEq
  exact not_lt_of_ge (least ηOrd smallerProto) (show ηOrd < δ from inside)

def BerkeleyCardinal (δ : V) : Prop :=
  InitialOrdinal δ ∧ (ω : V) ∈ δ ∧
    ∀ M, IsTransitive M → δ ∈ M → ∀ η ∈ δ,
      ∃ code κ, η ∈ κ ∧ κ ∈ δ ∧ CodedElementary M code ∧ CodedCriticalPoint M code κ

theorem compressed_yields_berkeley (verified : SetSentences.BerkeleyFormula E) :
    ∃ δ : V, BerkeleyCardinal δ := by
  obtain ⟨δ,proto,least⟩ := emitted_sentence_least_proto verified
  exact ⟨δ.val, least_proto_initial proto least, proto_uncountable proto, least_proto_cofinal proto least⟩

def initialOrdinalDef : SetTheorySemisentence 1 :=
  f“d. !IsOrdinal.dfn d ∧ ∀ e ∈ d,
    ¬∃ function, function ∈ !function.dfn d e ∧ d = !range.dfn function”

theorem initialOrdinal_defines : Defined (fun v : Fin 1 → V => InitialOrdinal (v 0)) initialOrdinalDef :=
  .mk fun v => by
    simp [initialOrdinalDef, InitialOrdinal, IsOrdinal.defined.iff, function.defined.iff, range.defined.iff, eq_comm]
    intro _
    constructor
    · intro law η ηIn f fIn
      exact (law η ηIn f).resolve_left (fun missing => missing fIn)
    · intro law η ηIn f
      by_cases fIn : f ∈ v 0 ^ η
      · exact .inr (law η ηIn f fIn)
      · exact .inl fIn

def berkeleyCardinalDef : SetTheorySemisentence 1 :=
  “d. !initialOrdinalDef d ∧ (∃ naturals, !isω naturals ∧ naturals ∈ d) ∧
    ∀ M, !IsTransitive.dfn M → d ∈ M → ∀ lower ∈ d,
      ∃ code k, lower ∈ k ∧ k ∈ d ∧ !codedElementaryDef M code ∧ !criticalPointDef M code k”

theorem berkeleyCardinal_defines : Defined (fun v : Fin 1 → V => BerkeleyCardinal (v 0)) berkeleyCardinalDef :=
  .mk fun v => by simp [berkeleyCardinalDef, BerkeleyCardinal, initialOrdinal_defines.iff,
    IsTransitive.defined.iff, codedElementary_defines.iff, criticalPoint_defines.iff]

def berkeleySetAxiom : SetTheorySentence := “∃ d, !berkeleyCardinalDef d”

theorem berkeleySetAxiom_models :
    V↓[ℒₛₑₜ] ⊧ berkeleySetAxiom ↔ ∃ d : V, BerkeleyCardinal d := by
  simp [berkeleySetAxiom, models_iff, berkeleyCardinal_defines.iff]

end I0451.Logic.SetAssignments
