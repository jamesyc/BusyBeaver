module
public import ConcreteChallengeAxioms
public import SourceModelConsistency
public import ConcreteSourceTranslationSemantics
@[expose] public section
/-! Checked all-assignment semantics for the copied source language. -/
namespace PalomarZF209
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
universe u
@[simp] theorem pushValue_eq {V:Type u}(s:Nat→V)(x:V):pushValue s x=ZFR.pushValue s x := by
 funext i; cases i <;> rfl
@[simp] theorem toSource_eval {V:Type u}(E:V→V→Prop)(p:Formula)(s:Nat→V):
 ZFR.eval E (toSource p) s ↔ eval E p s := by
 induction p generalizing s <;>
  simp_all [toSource,eval,ZFR.eval,pushValue_eq]
@[simp] theorem ofSource_eval {V:Type u}(E:V→V→Prop)(p:ZFR.Formula)(s:Nat→V):
 eval E (ofSource p) s ↔ ZFR.eval E p s := by
 simpa only [toSource_ofSource] using (toSource_eval E (ofSource p) s).symm
/-- Exact arbitrary-relation source-model equivalence, not standard-only truth. -/
theorem model_iff_source {V:Type}(E:V→V→Prop):
 Model E ↔ ZFR.NDSemantics.AxiomsTrue E := by
 constructor
 · intro h p hp s
   have hh:=h (ofSource p) ((axiom_iff (ofSource p)).mpr (by simpa using hp)) s
   exact (ofSource_eval E p s).mp hh
 · intro h p hp s
   exact (toSource_eval E p s).mp (h (toSource p) ((axiom_iff p).mp hp) s)
/-- Existing Foundation ZF models satisfy the exact copied Challenge axioms. -/
theorem foundation_model_to_challenge {V:Type}
 [SetStructure V] [Nonempty V]
 [V↓[Language.set] ⊧* 𝗭𝗙] :
 Model (fun x y:V=>x∈y) :=
 (model_iff_source _).mpr (ZFR.NDSemantics.all_source_zf_axioms_valid V)
end PalomarZF209
