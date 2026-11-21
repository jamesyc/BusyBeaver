module
public import I0451.Logic.MovingOrdinals
public import I0451.Logic.FiniteFormulaEncoding

/-! The least proto-Berkeley ordinal has cofinally many possible
critical points in every transitive set containing it. Named parameter
envelopes let the proof restrict a single embedding to both domains. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode I0451.Logic.ZFModel I0451.Logic.SetFormulaPrograms

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

def criticalPointDef : SetTheorySemisentence 3 :=
  “M code k. k ∈ M ∧ ¬!atDef code k k ∧ ∀ x ∈ k, !atDef code x x”

theorem criticalPoint_defines :
    Defined (fun v : Fin 3 → V => CodedCriticalPoint (v 0) (v 1) (v 2)) criticalPointDef :=
  .mk fun v => by
    simp [criticalPointDef, CodedCriticalPoint, at_defines.iff]

def protoBerkeleyOrdinalDef : SetTheorySemisentence 1 :=
  “bound. !IsOrdinal.dfn bound ∧ ∀ M, !IsTransitive.dfn M → bound ∈ M →
    ∃ code k, k ∈ bound ∧ !codedElementaryDef M code ∧ !criticalPointDef M code k”

theorem protoBerkeleyOrdinal_defines :
    Defined (fun v : Fin 1 → V => ProtoBerkeleyOrdinal (v 0)) protoBerkeleyOrdinalDef :=
  .mk fun v => by
    simp [protoBerkeleyOrdinalDef, ProtoBerkeleyOrdinal, IsOrdinal.defined.iff, IsTransitive.defined.iff,
      codedElementary_defines.iff, criticalPoint_defines.iff]

theorem CodedElementary.restrict_critical {D M code k : V} (large : CodedElementary D code)
    (bigTransitive : IsTransitive D) (smallTransitive : IsTransitive M) (mIn : M ∈ D)
    (fixed : At E code M M) (critical : CodedCriticalPoint D code k) (kIn : k ∈ M) :
    CodedElementary M (restrictedGraph code M) ∧ CodedCriticalPoint M (restrictedGraph code M) k := by
  obtain ⟨j, decoded, elementary⟩ := large.decoded_elementary
  have included := bigTransitive.transitive M mIn
  let m : Domain E D := ⟨M,mIn⟩
  have fixedM : j m = m := Subtype.ext ((decoded.at_iff m _).mp fixed)
  have preserves (x : V) (xM : x ∈ M) (y : V) (read : At E code x y) : y ∈ M := by
    let point : Domain E D := ⟨x,included x xM⟩
    have inside := (elementary.mem_iff point m).mp xM
    rw [fixedM] at inside
    exact ((decoded.at_iff point _).mp read) ▸ inside
  refine ⟨large.restrictGraph smallTransitive included mIn fixed preserves, kIn, ?_, ?_⟩
  · intro h
    exact critical.2.1 ((restrictedGraph_at _ _ _ _).mp h).2.2
  · intro x below
    have xIn := smallTransitive.transitive k kIn x below
    exact (restrictedGraph_at _ _ _ _).mpr ⟨xIn,xIn,critical.2.2 x below⟩

theorem coded_envelope_pair (x y : V) :
    ∃ D, IsTransitive D ∧ x ∈ D ∧ y ∈ D ∧
      ∀ code, CodedElementary D code → At E code x x ∧ At E code y y := by
  obtain ⟨D, marked, transitive, fixed⟩ := parameterEnvelope_fixes ⟨x,y⟩ₖ
  obtain ⟨xIn,yIn⟩ := pair_components_in transitive marked
  refine ⟨D,transitive,xIn,yIn,fun code elementaryCode => ?_⟩
  obtain ⟨j, decoded, elementary⟩ := elementaryCode.decoded_elementary
  let a : Domain E D := ⟨x,xIn⟩
  let b : Domain E D := ⟨y,yIn⟩
  obtain ⟨hx,hy⟩ := elementary_fixed_pair_components transitive elementary
    (p := ⟨⟨x,y⟩ₖ,marked⟩) (x := a) (y := b) rfl (fixed j elementary)
  exact ⟨(decoded.at_iff a _).mpr (congrArg Subtype.val hx),
    (decoded.at_iff b _).mpr (congrArg Subtype.val hy)⟩

theorem coded_envelope_three (x y z : V) :
    ∃ D, IsTransitive D ∧ x ∈ D ∧ y ∈ D ∧ z ∈ D ∧
      ∀ code, CodedElementary D code → At E code x x ∧ At E code y y ∧ At E code z z := by
  obtain ⟨D, transitive, xIn, pairIn, fixed⟩ := coded_envelope_pair x ⟨y,z⟩ₖ
  obtain ⟨yIn,zIn⟩ := pair_components_in transitive pairIn
  refine ⟨D,transitive,xIn,yIn,zIn,fun code elementaryCode => ?_⟩
  obtain ⟨j,decoded,elementary⟩ := elementaryCode.decoded_elementary
  let p : Domain E D := ⟨⟨y,z⟩ₖ,pairIn⟩
  let a : Domain E D := ⟨y,yIn⟩
  let b : Domain E D := ⟨z,zIn⟩
  have pairFixed : j p = p := Subtype.ext ((decoded.at_iff p _).mp (fixed code elementaryCode).2)
  obtain ⟨ya,zb⟩ := elementary_fixed_pair_components transitive elementary (p := p) (x := a) (y := b) rfl pairFixed
  exact ⟨(fixed code elementaryCode).1, (decoded.at_iff a _).mpr (congrArg Subtype.val ya),
    (decoded.at_iff b _).mpr (congrArg Subtype.val zb)⟩

private theorem proto_of_successor {d η : V} (proto : ProtoBerkeleyOrdinal d) (eq : d = succ η)
    (ordinal : IsOrdinal η) : ProtoBerkeleyOrdinal η := by
  refine ⟨ordinal, fun M transitive inM => ?_⟩
  obtain ⟨D, transD, MIn, dIn, _, keeps⟩ := coded_envelope_three M d η
  obtain ⟨code,k,kBelow,emb,crit⟩ := proto.2 D transD dIn
  obtain ⟨fixM, _, fixEta⟩ := keeps code emb
  have kEta : k ∈ η := by
    rw [eq] at kBelow
    rcases mem_succ_iff.mp kBelow with same | strict
    · subst k
      exact (crit.2.1 fixEta).elim
    · exact strict
  have kM := transitive.transitive η inM k kEta
  obtain ⟨restricted, point⟩ := emb.restrict_critical transD transitive MIn fixM crit kM
  exact ⟨restrictedGraph code M,k,kEta,restricted,point⟩

theorem least_proto_limit {δ : Ordinal V} (proto : ProtoBerkeleyOrdinal δ.val)
    (least : ∀ η : Ordinal V, ProtoBerkeleyOrdinal η.val → δ ≤ η) :
    ∀ η ∈ (δ : V), succ η ∈ (δ : V) := by
  intro η earlier
  let first := (IsOrdinal.of_mem earlier).toOrdinal
  have bound : first.succ ≤ δ := by
    intro x inside
    rcases mem_succ_iff.mp inside with rfl | before
    · exact earlier
    · exact δ.ordinal.toIsTransitive.transitive η earlier x before
  rcases lt_or_eq_of_le bound with below | equal
  · exact below
  · have exactSucc : δ.val = succ η := (congrArg Ordinal.val equal).symm
    exact (not_lt_of_ge (least first (proto_of_successor proto exactSucc first.ordinal))
      (show first < δ from earlier)).elim

theorem least_proto_cofinal {δ : Ordinal V} (proto : ProtoBerkeleyOrdinal δ.val)
    (least : ∀ η : Ordinal V, ProtoBerkeleyOrdinal η.val → δ ≤ η) :
    ∀ M, IsTransitive M → δ.val ∈ M → ∀ η ∈ (δ : V),
      ∃ code k, η ∈ k ∧ k ∈ (δ : V) ∧ CodedElementary M code ∧ CodedCriticalPoint M code k := by
  classical
  intro M transM dM η ηBound
  by_contra failure
  let larger : Ordinal V := (IsOrdinal.of_mem ηBound).toOrdinal.succ
  have largerD : larger < δ := least_proto_limit proto least η ηBound
  have newProto : ProtoBerkeleyOrdinal larger.val := by
    refine ⟨larger.ordinal, fun N transN largerN => ?_⟩
    obtain ⟨D,transD,mIn,nIn,keeps⟩ := coded_envelope_pair M N
    have dIn := transD.transitive M mIn δ.val dM
    obtain ⟨code,k,kBelow,emb,crit⟩ := proto.2 D transD dIn
    obtain ⟨fixedM,fixedN⟩ := keeps code emb
    have kM := transM.transitive _ dM k kBelow
    obtain ⟨largeInM, critM⟩ := emb.restrict_critical transD transM mIn fixedM crit kM
    have smaller : k ∈ larger.val := by
      let ko := (IsOrdinal.of_mem kBelow).toOrdinal
      let bound := (IsOrdinal.of_mem ηBound).toOrdinal
      rcases lt_trichotomy ko bound with below | same | higher
      · exact mem_succ_iff.mpr (.inr below)
      · exact mem_succ_iff.mpr (.inl (congrArg Ordinal.val same))
      · exact (failure ⟨restrictedGraph code M,k,higher,kBelow,largeInM,critM⟩).elim
    have kN := transN.transitive _ largerN k smaller
    obtain ⟨largeInN, critN⟩ := emb.restrict_critical transD transN nIn fixedN crit kN
    exact ⟨restrictedGraph code N,k,smaller,largeInN,critN⟩
  exact not_lt_of_ge (least larger newProto) largerD

theorem emitted_sentence_least_proto (holds : SetSentences.BerkeleyFormula E) :
    ∃ δ : Ordinal V, ProtoBerkeleyOrdinal δ.val ∧
      ∀ η : Ordinal V, ProtoBerkeleyOrdinal η.val → δ ≤ η := by
  obtain ⟨bound, proto⟩ := berkeleyFormula_has_ordinal_bound holds
  exact exists_minimal ProtoBerkeleyOrdinal protoBerkeleyOrdinal_defines.to_definable
    ⟨proto.1.toOrdinal, proto⟩

end I0451.Logic.SetAssignments
