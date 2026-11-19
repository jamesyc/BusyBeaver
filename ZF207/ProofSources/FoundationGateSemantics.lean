module
public import FoundationSourceEncoding
public import ScottHull
public import LiteralPositiveBridge
public import ExactGateSemantics
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open C207Soundness

universe u

theorem formula_eval_decode {V : Type u} (mem : V → V → Prop) (a : Nat) (s : Nat → V) :
 C207Soundness.Formula.eval mem (decodeNat a) s ↔ evalCode mem a s := Iff.rfl

theorem eval_positivePointed_distinct {V : Type u} (mem : V → V → Prop)
 (a d h : Nat) (had : a≠d) (hah : a≠h) (hdh : d≠h) (s : Nat → V) :
 ZFR.eval mem (positivePointedSource a d h) s ↔
 ∃ C, (∀ z, mem z C → ∃ p,
   evalCode mem a (update (update s d p) h z) ∧
   ∀ u, (∀ w,mem w u → mem w z) → ∀ v,
     evalCode mem a (update (update s d u) h v) →
     ∃ w,evalCode mem a (update (update s d u) h w) ∧ mem w C) ∧
   (evalCode mem a s → mem (s h) C) := by
 simp only [positivePointedSource,positiveMemberSource,ZFR.eval,eval_translate,pushed_binding]
 change (∃ C, _) ↔ _
 simp only [formula_eval_decode,update_same,update_shadow,
   evalCode_erase_self_under_two a h d hah had,
   evalCode_erase_self_under_two a d h had hah,
   update_commute s h d (Ne.symm hdh),evalCode_self_independent]
 simp [bindName,pushValue,update,had,hah,hdh,Ne.symm had,Ne.symm hah,Ne.symm hdh]
 all_goals simp only [update_commute (fun j => s j) h d (Ne.symm hdh)]

theorem named_eval_definable {V : Type*} [SetStructure V]
 (A : C207Soundness.Formula) {k : Nat} (s : Nat → (Fin k → V) → V)
 (hs : ∀ i, Language.DefinableFunction (L := Language.set) (s i)) :
 Language.Definable (L := Language.set) (fun v => A.eval (fun x y : V => x ∈ y) (fun i => s i v)) := by
 induction A generalizing k with
 | truth => exact Language.Definable.const True
 | mem i j => exact Language.DefinableRel.comp (P := Membership.mem) (hs j) (hs i)
 | eq i j => exact Language.DefinableRel.comp (P := Eq) (hs i) (hs j)
 | imp A B ia ib => exact (ia s hs).imp (ib s hs)
 | all i A ih =>
   apply Language.Definable.all
   apply ih
   intro j
   by_cases he : j=i
   · subst j
     simpa only [update,if_pos] using
       (Language.DefinableFunction.projection (L := ℒₛₑₜ) (M := V) (k := k+1) 0)
   · change Language.DefinableFunction (L := Language.set) (fun v : Fin (k+1) → V => update (fun j => s j (fun l => v l.succ)) i (v 0) j)
     simp only [update,he,if_neg]
     exact Language.DefinableFunction.substitution (hs j)
       (fun l => Language.DefinableFunction.projection l.succ)

theorem decoded_relation_definable {V : Type*} [SetStructure V]
 (a d h : Nat) (s : Nat → V) :
 ℒₛₑₜ-relation (fun u v => evalCode (fun x y : V => x ∈ y) a (update (update s d u) h v)) := by
 apply named_eval_definable (decodeNat a)
 intro j
 by_cases hjh : j=h
 · subst j
   simpa only [update,if_pos] using
     (Language.DefinableFunction.projection (L := ℒₛₑₜ) (M := V) (k := 2) 1)
 · by_cases hjd : j=d
   · subst j
     simpa [update,hjh] using
       (Language.DefinableFunction.projection (L := ℒₛₑₜ) (M := V) (k := 2) 0)
   · simpa [update,hjh,hjd] using
       (Language.DefinableFunction.const (L := ℒₛₑₜ) (k := 2) (s j))

theorem source_positive_valid {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
 (a d h : Nat) (had : a≠d) (hah : a≠h) (hdh : d≠h) (s : Nat → V) :
 ZFR.eval (fun x y : V => x ∈ y) (positivePointedSource a d h) s := by
 let R := fun u v => evalCode (fun x y : V => x ∈ y) a (update (update s d u) h v)
 have hR : ℒₛₑₜ-relation R := decoded_relation_definable a d h s
 obtain ⟨C,hpoint,hC⟩ := ZF207Experiment.binary_pointed_hull R hR (s d) (s h)
 apply (eval_positivePointed_distinct _ a d h had hah hdh s).mpr
 refine ⟨C,?_,?_⟩
 · intro z hz
   obtain ⟨⟨p,hp⟩,hc⟩ := hC z hz
   refine ⟨p,hp,?_⟩
   intro u hu v hv
   obtain ⟨w,hw,hRuw⟩ := hc u (by intro t ht; exact hu t ht) ⟨v,hv⟩
   exact ⟨w,hRuw,hw⟩
 · intro ha
   apply hpoint
   have hu : update s d (s d) = s := by funext j; by_cases he : j=d <;> simp_all [update]
   have hv : update s h (s h) = s := by funext j; by_cases he : j=h <;> simp_all [update]
   simpa only [R,hu,hv] using ha

def mixedAssignment {V : Type*} (n : Nat) (b : Fin n → V) (s : Nat → V) (i : Nat) : V :=
 if hi : i<n then b ⟨i,hi⟩ else s (i-n)

theorem sourceTerm_val {V : Type*} [SetStructure V] (n i : Nat) (b : Fin n → V) (s : Nat → V) :
 Semiterm.val b s (sourceTerm n i) = mixedAssignment n b s i := by
 unfold sourceTerm mixedAssignment
 split <;> rfl

theorem mixedAssignment_cons {V : Type*} (n : Nat) (b : Fin n → V) (s : Nat → V) (x : V) :
 mixedAssignment (n+1) (x :> b) s = pushValue (mixedAssignment n b s) x := by
 funext i
 cases i with
 | zero => simp [mixedAssignment,pushValue]
 | succ i =>
   simp only [mixedAssignment,pushValue,Nat.succ_lt_succ_iff]
   split <;> rename_i hi
   · rfl
   · simp [Nat.succ_sub_succ_eq_sub]

theorem ofSource_eval {V : Type*} [SetStructure V] (p : ZFR.Formula)
 (n : Nat) (b : Fin n → V) (s : Nat → V) :
 Semiformula.Eval b s (ofSource n p) ↔
 ZFR.eval (fun x y : V => x ∈ y) p (mixedAssignment n b s) := by
 induction p generalizing n with
 | bot => rfl
 | mem i j =>
   change (Semiterm.val b s (sourceTerm n i) ∈ Semiterm.val b s (sourceTerm n j)) ↔ _
   rw [sourceTerm_val,sourceTerm_val]; rfl
 | eq i j =>
   change (Semiterm.val b s (sourceTerm n i) = Semiterm.val b s (sourceTerm n j)) ↔ _
   rw [sourceTerm_val,sourceTerm_val]; rfl
 | and p q ip iq =>
   change (Semiformula.Eval b s (ofSource n p) ∧ Semiformula.Eval b s (ofSource n q)) ↔ _
   exact and_congr (ip n b) (iq n b)
 | or p q ip iq =>
   change (Semiformula.Eval b s (ofSource n p) ∨ Semiformula.Eval b s (ofSource n q)) ↔ _
   exact or_congr (ip n b) (iq n b)
 | imp p q ip iq =>
   change (Semiformula.Eval b s (Semiformula.neg (ofSource n p)) ∨ Semiformula.Eval b s (ofSource n q)) ↔ _
   have hn : Semiformula.Eval b s (Semiformula.neg (ofSource n p)) ↔ ¬Semiformula.Eval b s (ofSource n p) := by
     change Semiformula.EvalAux (standardStructure V) s b (Semiformula.neg (ofSource n p)) ↔
       ¬Semiformula.EvalAux (standardStructure V) s b (ofSource n p)
     rw [← Semiformula.neg_eq, Semiformula.EvalAux_neg]
   rw [hn,ip,iq]
   exact (imp_iff_not_or).symm
 | all p ip =>
   change (∀ x : V, Semiformula.Eval (x :> b) s (ofSource (n+1) p)) ↔ _
   apply forall_congr'; intro x
   rw [ip,mixedAssignment_cons]
 | ex p ip =>
   change (∃ x : V, Semiformula.Eval (x :> b) s (ofSource (n+1) p)) ↔ _
   apply exists_congr; intro x
   rw [ip,mixedAssignment_cons]

theorem ofSource_positive_valid {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
 (a d h : Nat) (had : a≠d) (hah : a≠h) (hdh : d≠h) (s : Nat → V) :
 (ofSource 0 (positivePointedSource a d h)).Evalf s := by
 apply (ofSource_eval _ 0 ![] s).mpr
 exact source_positive_valid a d h had hah hdh _

/-- An ACTUAL pinned Foundation theory proof, obtained from validity in every
arbitrary ZF model via its checked equality-aware completeness theorem. -/
theorem foundation_positive_proof (a d h : Nat) (had : a≠d) (hah : a≠h) (hdh : d≠h) :
 𝗭𝗙 ⊢ (ofSource 0 (positivePointedSource a d h)).univCl := by
 apply SetTheory.complete.{0}
 intro V instV neV modelV
 rw [models_iff_proposition]
 intro s
 exact ofSource_positive_valid a d h had hah hdh s

end ZFR.FoundationBridge
