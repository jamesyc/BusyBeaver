module
public import ZF192Support.Calculus.Internal.TraceRules
public import ZF192Support.Calculus.Standard.Kernel
public import ZF192Support.Calculus.Standard.HistoryRules
@[expose] public section

namespace ZF192Support.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open ZFR.ArithmeticRepresentation CCodeSoundness

lemma codes_nat_head {f : CKernel.Generic.Codes ℕ → ℕ} :
    f (ZF192Support.Internal.codes : CKernel.Generic.Codes ℕ) = f CKernel.natCodes := by
  rw [ZF192Support.Internal.codes_nat]

lemma imp_nat (a b : ℕ) : ZF192Support.Internal.imp a b = impCode a b := by
  have := congrArg (fun K : CKernel.Generic.Codes ℕ => K.imp a b) ZF192Support.Internal.codes_nat
  simpa [ZF192Support.Internal.codes, CKernel.natCodes] using this

lemma all_nat (i b : ℕ) : ZF192Support.Internal.all i b = allCode i b := by
  have := congrArg (fun K : CKernel.Generic.Codes ℕ => K.all i b) ZF192Support.Internal.codes_nat
  simpa [ZF192Support.Internal.codes, CKernel.natCodes] using this

lemma cAxiom_nat {r : ℕ} (h : cAxiom r) : ExactProvable r := by
  obtain ⟨a, d, h', u, H⟩ := h
  rw [ZF192Support.Internal.codes_nat] at H
  rcases H with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨hu, rfl⟩ | ⟨hd, hh, rfl⟩
  · exact CProofSearch.proved_zero
  · exact CKernel.natSys.h6 d a h'
  · exact CKernel.natSys.h5 d h'
  · exact CKernel.natSys.h4 h' d a
  · exact CKernel.natSys.h3 h' d a
  · exact CKernel.natSys.h2 d a h'
  · exact CKernel.natSys.h1 d h'
  · have hu' : u = d ∨ u < d := hu
    exact CKernel.natSys.r8 d a h' u (show u ≤ d from hu'.elim (fun h => h ▸ Nat.le_refl _) Nat.le_of_lt)
  · exact CKernel.natSys.gate h' d a hh hd

private theorem cAxiom_of_exactAxiom {n : Nat} (hn : ExactAxiom n) : cAxiom n := by
  rcases hn with rfl | ⟨a, d, h, u, ha⟩
  · exact ⟨0, 0, 0, 0, Or.inl rfl⟩
  · refine ⟨a, d, h, u, ?_⟩
    rw [ZF192Support.Internal.codes_nat]
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | ⟨hu, rfl⟩ | ⟨had, hah, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · have hu' : u = d ∨ u < d := Nat.eq_or_lt_of_le hu
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu', rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨had, hah, rfl⟩)))))))

private noncomputable def exactHistoryCode : List Nat → Nat :=
  List.foldr modelListCons 0

private theorem member_exactHistoryCode {x : Nat} {xs : List Nat} :
    modelMember x (exactHistoryCode xs) ↔ x ∈ xs := by
  induction xs with
  | nil => simp [exactHistoryCode, modelMember, modelMemberCode_zero]
  | cons a xs ih =>
    change modelMember x (modelListCons a (exactHistoryCode xs)) ↔ x ∈ a :: xs
    rw [modelMember_cons, ih, List.mem_cons, eq_comm]

private theorem trace_exactHistoryCode {xs : List Nat} (hx : ExactHistory xs) :
    modelTrace cRule (exactHistoryCode xs) := by
  induction hx with
  | nil => exact modelTrace_zero _
  | axRule n xs h ha ih =>
    exact (modelTrace_cons cRule n _).mpr ⟨ih, Or.inl (cAxiom_of_exactAxiom ha)⟩
  | mp b c xs h hb hi ih =>
    exact (modelTrace_cons cRule c _).mpr
      ⟨ih, Or.inr (Or.inl ⟨b, member_exactHistoryCode.mpr hb, by rw [imp_nat]; exact member_exactHistoryCode.mpr hi⟩)⟩
  | gen i b xs h hb ih =>
    exact (modelTrace_cons cRule _ _).mpr
      ⟨ih, Or.inr (Or.inr ⟨i, b, member_exactHistoryCode.mpr hb, (all_nat i b).symm⟩)⟩

/-- A standard derivation encodes a trace of the same calculus used by the model compiler. -/
theorem trace_of_exactProvable {n : Nat} (h : ExactProvable n) :
    ∃ p : Nat, modelTrace cRule p ∧ modelMember n p := by
  obtain ⟨xs, hx, hm⟩ := h
  exact ⟨exactHistoryCode xs, trace_exactHistoryCode hx, member_exactHistoryCode.mpr hm⟩

/-- Every entry of a standard trace is a theorem of the machine's calculus. -/
theorem trace_provable : ∀ p : ℕ, modelTrace cRule p → ∀ x, modelMember x p → ExactProvable x := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp x hx
    by_cases hz : p = 0
    · subst hz; simp [modelMember, modelMemberCode_zero] at hx
    have hpos : 0 < p := Nat.pos_of_ne_zero hz
    have he : p = modelListCons (modelListHead p) (modelListTail p) :=
      (modelList_reconstruct p hpos).symm
    rw [he, modelTrace_cons] at hp
    rw [he, modelMember_cons] at hx
    have ht := modelListTail_lt p hpos
    have ihT := ih _ ht hp.1
    rcases hx with rfl | hx
    · rcases hp.2 with hax | ⟨b, hb, hi⟩ | ⟨i, b, hb, hr⟩
      · exact cAxiom_nat hax
      · exact CKernel.natSys.mp (ihT b hb) (by simpa [imp_nat, CKernel.natSys, CKernel.natCodes] using ihT _ hi)
      · rw [hr, all_nat]; exact CKernel.natSys.gen i (ihT b hb)
    · exact ihT x hx

theorem exactProvable_of_cprov {x : ℕ} (h : CProv x) : ExactProvable x := by
  obtain ⟨p, hp, hm⟩ := (D_iff x).mp h
  exact trace_provable p hp x hm

end ZF192Support.Halting
