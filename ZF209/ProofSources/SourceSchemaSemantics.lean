module
public import FoundationSemanticCertificates
public import SourceModelConsistency
public import DirectWitnessCoverage
public import Foundation.FirstOrder.SetTheory.ZF.ZF
@[expose] public section
namespace ZFR.NDSemantics
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory ZFR.FoundationBridge
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "E" => (fun x y : V => x ∈ y)

noncomputable def parameterFormula (n : Nat) (p : Formula) (s : Nat → V) : SetTheorySemiformula V n :=
 (Rew.rewriteMap s) ▹ ofSource n p

theorem parameter_eval (n : Nat) (p : Formula) (s : Nat → V) (b : Fin n → V) :
 (parameterFormula n p s).Eval b id ↔ eval E p (certificateAssignment n b s) := by
 unfold parameterFormula
 rw [Semiformula.eval_rewriteMap]
 exact certificate_ofSource_eval p n b s

theorem parameter_one (p : Formula) (s : Nat → V) (x : V) :
 (parameterFormula 1 p s).Eval ![x] id ↔ eval E p (pushValue s x) := by
 rw [parameter_eval]
 have he : certificateAssignment 1 ![x] s = pushValue s x := by
   funext i; cases i with
   | zero => simp [certificateAssignment,pushValue]
   | succ i => simp [certificateAssignment,pushValue]
 rw [he]

theorem parameter_two (p : Formula) (s : Nat → V) (x y : V) :
 (parameterFormula 2 p s).Eval ![x,y] id ↔ eval E p (pushValue (pushValue s y) x) := by
 rw [parameter_eval]
 have he : certificateAssignment 2 ![x,y] s = pushValue (pushValue s y) x := by
   funext i; cases i with
   | zero => simp [certificateAssignment,pushValue]
   | succ i => cases i with
     | zero => simp [certificateAssignment,pushValue]
     | succ i => simp [certificateAssignment,pushValue]
 rw [he]

theorem sep_eval (p : Formula) (s : Nat → V) (X Y x : V) :
 eval E (rename sepIndex p) (pushValue (pushValue (pushValue s X) Y) x) ↔
 eval E p (pushValue s x) := by
 rw [FiniteCode.eval_rename]
 have he : (pushValue (pushValue (pushValue s X) Y) x) ∘ sepIndex = pushValue s x := by
  funext i; cases i <;> simp [Function.comp_def,sepIndex,pushValue]
 rw [he]

theorem separation_open_valid (p : Formula) (s : Nat → V) :
 eval E (separationFormula (rename sepIndex p)) s := by
 change ∀ X : V, ∃ Y : V, ∀ x : V,
  (x ∈ Y → x ∈ X ∧ eval E (rename sepIndex p) (pushValue (pushValue (pushValue s X) Y) x)) ∧
  (x ∈ X ∧ eval E (rename sepIndex p) (pushValue (pushValue (pushValue s X) Y) x) → x ∈ Y)
 intro X
 obtain ⟨Y,hY⟩ := separation_exists_eval X (parameterFormula 1 p s)
 refine ⟨Y,?_⟩
 intro x
 rw [sep_eval]
 have h := hY x
 rw [parameter_one] at h
 exact ⟨h.mp,h.mpr⟩

theorem allPrefix_valid (p : Formula) (h : ∀ s : Nat → V, eval E p s) (n : Nat) (s : Nat → V) :
 eval E (allPrefix n p) s := by
 induction n generalizing s with
 | zero => exact h s
 | succ n ih => exact fun x => ih (pushValue s x)

theorem separation_schema_valid (p : Formula) (n : Nat) (s : Nat → V) :
 eval E (separationSchema n p) s := allPrefix_valid _ (separation_open_valid p) n s
theorem numeric_separation_valid (p : Formula)
 (h : numericClosedSeparation (encodeFormula p)) (s : Nat → V) : eval E p s := by
 obtain ⟨_,phi,n,hphi,he⟩ := h
 obtain ⟨q,hq,hb⟩ := RosserDirect.WitnessCoverage.bounded_code_is_formula phi (n+1) hphi
 rw [← hq,numericSeparationCode_encode] at he
 have eq := encodeFormula_injective he
 subst p
 exact separation_schema_valid q n s

noncomputable def sourceRelation (p : Formula) (s : Nat → V) (x y : V) : Prop :=
 eval E p (pushValue (pushValue s y) x)

theorem relation_definable (p : Formula) (s : Nat → V) : ℒₛₑₜ-relation (sourceRelation p s) := by
 refine ⟨parameterFormula 2 p s,?_⟩
 intro v
 have hv : v = ![v 0,v 1] := by
  funext k; have hk : k=0 ∨ k=1 := by omega
  rcases hk with rfl | rfl <;> rfl
 rw [hv]
 exact parameter_two p s (v 0) (v 1)

/-- ZF replacement for a definable partial functional relation, obtained by
separating its domain before applying the library's total-on-domain theorem. -/
theorem partial_replacement_exists (R : V → V → Prop)
 (hR : ℒₛₑₜ-relation R) (unique : ∀ x y z, R x y → R x z → y=z) (X : V) :
 ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R x y := by
 letI := hR
 obtain ⟨D,hD⟩ := separation_exists X (fun x => ∃ y, R x y) (by definability)
 have total : ∀ x ∈ D, ∃! y, R x y := by
  intro x hx
  obtain ⟨y,hy⟩ := ((hD x).mp hx).2
  exact ⟨y,hy,fun z hz => unique x z y hz hy⟩
 obtain ⟨Y,hY⟩ := replacement_rel_exists_of_mem_existsUnique D R total hR
 refine ⟨Y,?_⟩
 intro y
 rw [hY]
 constructor
 · rintro ⟨x,hx,hr⟩; exact ⟨x,((hD x).mp hx).1,hr⟩
 · rintro ⟨x,hx,hr⟩; exact ⟨x,(hD x).mpr ⟨hx,y,hr⟩,hr⟩

theorem repA_eval (p : Formula) (s : Nat → V) (x y z : V) :
 eval E (rename repAIndex p) (pushValue (pushValue (pushValue s x) y) z) ↔ sourceRelation p s x y := by
 rw [FiniteCode.eval_rename]
 have he : (pushValue (pushValue (pushValue s x) y) z) ∘ repAIndex = pushValue (pushValue s y) x := by
  funext i; cases i with
  | zero => simp [Function.comp_def,repAIndex,pushValue]
  | succ i => cases i <;> simp [Function.comp_def,repAIndex,pushValue]
 rw [he]; rfl

theorem repB_eval (p : Formula) (s : Nat → V) (x y z : V) :
 eval E (rename repBIndex p) (pushValue (pushValue (pushValue s x) y) z) ↔ sourceRelation p s x z := by
 rw [FiniteCode.eval_rename]
 have he : (pushValue (pushValue (pushValue s x) y) z) ∘ repBIndex = pushValue (pushValue s z) x := by
  funext i; cases i with
  | zero => simp [Function.comp_def,repBIndex,pushValue]
  | succ i => cases i <;> simp [Function.comp_def,repBIndex,pushValue]
 rw [he]; rfl

theorem repC_eval (p : Formula) (s : Nat → V) (X Y y x : V) :
 eval E (rename repCIndex p) (pushValue (pushValue (pushValue (pushValue s X) Y) y) x) ↔ sourceRelation p s x y := by
 rw [FiniteCode.eval_rename]
 have he : (pushValue (pushValue (pushValue (pushValue s X) Y) y) x) ∘ repCIndex = pushValue (pushValue s y) x := by
  funext i; cases i with
  | zero => simp [Function.comp_def,repCIndex,pushValue]
  | succ i => cases i <;> simp [Function.comp_def,repCIndex,pushValue]
 rw [he]; rfl

theorem replacement_open_valid (p : Formula) (s : Nat → V) :
 eval E (replacementFormula (rename repAIndex p) (rename repBIndex p) (rename repCIndex p)) s := by
 intro functional
 have hu : ∀ x y z, sourceRelation p s x y → sourceRelation p s x z → y=z := by
  intro x y z hxy hxz
  exact functional x y z ((repA_eval p s x y z).mpr hxy) ((repB_eval p s x y z).mpr hxz)
 intro X
 obtain ⟨Y,hY⟩ := partial_replacement_exists (sourceRelation p s) (relation_definable p s) hu X
 refine ⟨Y,?_⟩
 intro y
 change (y ∈ Y → ∃ x, x ∈ X ∧ eval E (rename repCIndex p) (pushValue (pushValue (pushValue (pushValue s X) Y) y) x)) ∧
  ((∃ x, x ∈ X ∧ eval E (rename repCIndex p) (pushValue (pushValue (pushValue (pushValue s X) Y) y) x)) → y ∈ Y)
 simp only [repC_eval]
 exact ⟨(hY y).mp,(hY y).mpr⟩

theorem replacement_schema_valid (p : Formula) (n : Nat) (s : Nat → V) :
 eval E (replacementSchema n p) s := allPrefix_valid _ (replacement_open_valid p) n s

theorem numeric_replacement_valid (p : Formula)
 (h : numericClosedReplacement (encodeFormula p)) (s : Nat → V) : eval E p s := by
 obtain ⟨_,phi,n,hphi,he⟩ := h
 obtain ⟨q,hq,hb⟩ := RosserDirect.WitnessCoverage.bounded_code_is_formula phi (n+2) hphi
 rw [← hq,numericReplacementCode_encode] at he
 have eq := encodeFormula_injective he
 subst p
 exact replacement_schema_valid q n s

end ZFR.NDSemantics
