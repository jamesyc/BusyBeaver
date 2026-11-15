module
public import FoundationAxiomBridge
public import FormulaEquality
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

def equalitySourceContext : Context := [zfrRefl,zfrSym,zfrTrans,zfrEqElem]

theorem equalitySourceContext_exact : EqualityContext equalitySourceContext :=
 ⟨by simp [equalitySourceContext],by simp [equalitySourceContext],
 by simp [equalitySourceContext],by simp [equalitySourceContext]⟩

theorem equalitySourceContext_in_zfr : ∀ p, p ∈ equalitySourceContext → sourceZfrAxiom (encodeFormula p) := by
 intro p hp
 simp only [equalitySourceContext,List.mem_cons,List.not_mem_nil,or_false] at hp
 rcases hp with rfl | rfl | rfl | rfl <;>
   simp [sourceZfrAxiom,sourceZfrFixed,fixedRefl,fixedSym,fixedTrans,fixedEqElem,
     zfrRefl,zfrSym,zfrTrans,zfrEqElem]

theorem eq_refl_exact : axiomSource (Theory.Eq.refl Language.set) = fixedRefl := rfl

theorem eq_sym_equiv (Γ : Context) :
 NDEquiv Γ (axiomSource (Theory.Eq.symm Language.set)) fixedSym := by
 apply NDEquiv.all; apply NDEquiv.all
 exact toSource_arrow_equiv _
   (Semiformula.rel .eq ![.bvar 1,.bvar 0] : Semiformula Language.set Nat 2)
   (.rel .eq ![.bvar 0,.bvar 1])

theorem eq_trans_equiv (Γ : Context) :
 NDEquiv Γ (axiomSource (Theory.Eq.trans Language.set)) fixedTrans := by
 apply NDEquiv.all; apply NDEquiv.all; apply NDEquiv.all
 apply (toSource_arrow_equiv _
   (Semiformula.rel .eq ![.bvar 2,.bvar 1] : Semiformula Language.set Nat 3)
   (.or (.nrel .eq ![.bvar 1,.bvar 0]) (.rel .eq ![.bvar 2,.bvar 0]))).trans
 exact (NDEquiv.refl _ _).imp (toSource_arrow_equiv _
   (Semiformula.rel .eq ![.bvar 1,.bvar 0] : Semiformula Language.set Nat 3)
   (.rel .eq ![.bvar 2,.bvar 0]))

def relationExtAnte : Semiformula Language.set Nat 4 :=
 .and (.rel .eq ![.bvar 0,.bvar 2]) (.and (.rel .eq ![.bvar 1,.bvar 3]) .verum)

theorem relationExt_open_equiv (Γ : Context) (r : Language.Set.Rel 2) :
 NDEquiv Γ
 (toSource (.or (Semiformula.neg relationExtAnte)
   (.or (.nrel r ![.bvar 0,.bvar 1]) (.rel r ![.bvar 2,.bvar 3]))))
 (.imp (.and (.eq 0 2) (.and (.eq 1 3) (.imp .bot .bot)))
   (.imp (atom (n := 4) r ![.bvar 0,.bvar 1]) (atom (n := 4) r ![.bvar 2,.bvar 3]))) := by
 apply (toSource_arrow_equiv Γ relationExtAnte _).trans
 exact (NDEquiv.refl Γ _).imp (toSource_arrow_equiv Γ
   (Semiformula.rel r ![.bvar 0,.bvar 1] : Semiformula Language.set Nat 4)
   (.rel r ![.bvar 2,.bvar 3]))

theorem nd_mem_ext_actual {Γ : Context} (ctx : EqualityContext Γ) :
 ND (.seq Γ (axiomSource (Theory.Eq.relExt (L := Language.set) Language.Set.Rel.mem))) := by
 apply ND.allI; apply ND.allI; apply ND.allI; apply ND.allI
 apply ND.ie (relationExt_open_equiv _ .mem).2
 apply ND.ii
 have he := nd_eqElem_instance ctx.shift.shift.shift.shift.elem 0 1 2 3
 have ha : ND (.seq
   (.and (.eq 0 2) (.and (.eq 1 3) (.imp .bot .bot)) ::
   shiftContext (shiftContext (shiftContext (shiftContext Γ))))
   (.and (.eq 0 2) (.and (.eq 1 3) (.imp .bot .bot)))) := ND.ctx (by simp)
 exact ND.ie (ND.ie he.weaken_cons (ND.ce1 ha)) (ND.ce1 (ND.ce2 ha))

theorem nd_eq_ext_actual {Γ : Context} (ctx : EqualityContext Γ) :
 ND (.seq Γ (axiomSource (Theory.Eq.relExt (L := Language.set) Language.Set.Rel.eq))) := by
 apply ND.allI; apply ND.allI; apply ND.allI; apply ND.allI
 apply ND.ie (relationExt_open_equiv _ .eq).2
 apply ND.ii; apply ND.ii
 let Δ := (.eq 0 1 ::
   .and (.eq 0 2) (.and (.eq 1 3) (.imp .bot .bot)) ::
   shiftContext (shiftContext (shiftContext (shiftContext Γ))))
 have hc : EqualityContext Δ := ctx.shift.shift.shift.shift.cons _ |>.cons _
 have ha : ND (.seq Δ (.and (.eq 0 2) (.and (.eq 1 3) (.imp .bot .bot)))) := ND.ctx (by simp [Δ])
 have h02 : ND (.seq Δ (.eq 0 2)) := ND.ce1 ha
 have h13 : ND (.seq Δ (.eq 1 3)) := ND.ce1 (ND.ce2 ha)
 have h01 : ND (.seq Δ (.eq 0 1)) := ND.ctx (by simp [Δ])
 exact eq_trans hc (eq_trans hc (eq_symm hc h02) h01) h13

theorem source_eq_refl : SourceTheorem (axiomSource (Theory.Eq.refl Language.set)) := by
 rw [eq_refl_exact]
 exact fixed_source_theorem fixedRefl (by simp [sourceZfrFixed])

theorem source_eq_sym : SourceTheorem (axiomSource (Theory.Eq.symm Language.set)) :=
 source_theorem_of_equiv fixedSym _ (fixed_source_theorem _ (by simp [sourceZfrFixed]))
   (fun Γ => (eq_sym_equiv Γ).symm)

theorem source_eq_trans : SourceTheorem (axiomSource (Theory.Eq.trans Language.set)) :=
 source_theorem_of_equiv fixedTrans _ (fixed_source_theorem _ (by simp [sourceZfrFixed]))
   (fun Γ => (eq_trans_equiv Γ).symm)

/-- Every actual equality axiom of the pinned set-theory language has an
actual finite source-ZFR proof. There are no function symbols. -/
theorem source_equality_axiom {p : SetTheorySentence}
 (hp : Theory.eqAxiom Language.set p) : SourceTheorem (axiomSource p) := by
 cases hp with
 | refl => exact source_eq_refl
 | symm => exact source_eq_sym
 | trans => exact source_eq_trans
 | funcExt f => exact Empty.elim f
 | relExt r =>
   cases r with
   | mem => exact ⟨equalitySourceContext,equalitySourceContext_in_zfr,nd_mem_ext_actual equalitySourceContext_exact⟩
   | eq => exact ⟨equalitySourceContext,equalitySourceContext_in_zfr,nd_eq_ext_actual equalitySourceContext_exact⟩

end ZFR.FoundationBridge
