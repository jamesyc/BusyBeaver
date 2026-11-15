module
public import Palomar209ZFDefinition
public import SourceND
public import NumericTheory
@[expose] public section
/-! Checked structural isomorphism for the standalone source presentation. -/
namespace PalomarZF209
def toSource : Formula → ZFR.Formula
 | .bot  => .bot 
 | .mem i j => .mem i j
 | .eq i j => .eq i j
 | .and a b => .and (toSource a) (toSource b)
 | .or a b => .or (toSource a) (toSource b)
 | .imp a b => .imp (toSource a) (toSource b)
 | .all a => .all (toSource a)
 | .ex a => .ex (toSource a)
def ofSource : ZFR.Formula → Formula
 | .bot  => .bot 
 | .mem i j => .mem i j
 | .eq i j => .eq i j
 | .and a b => .and (ofSource a) (ofSource b)
 | .or a b => .or (ofSource a) (ofSource b)
 | .imp a b => .imp (ofSource a) (ofSource b)
 | .all a => .all (ofSource a)
 | .ex a => .ex (ofSource a)

@[simp] theorem ofSource_toSource (p:Formula) : ofSource (toSource p)=p := by
 induction p <;> simp_all [toSource,ofSource]
@[simp] theorem toSource_ofSource (p:ZFR.Formula) : toSource (ofSource p)=p := by
 induction p <;> simp_all [toSource,ofSource]
theorem toSource_injective : Function.Injective toSource := by
 intro a b h; simpa using congrArg ofSource h
@[simp] theorem lift_eq (σ:Nat→Nat):lift σ=ZFR.lift σ := by
 funext n; cases n <;> rfl
@[simp] theorem substMap_eq (n:Nat):substMap n=ZFR.substMap n := by
 funext i; cases i <;> rfl
@[simp] theorem toSource_rename (σ:Nat→Nat)(p:Formula) :
 toSource (rename σ p)=ZFR.rename σ (toSource p) := by
 induction p generalizing σ <;> simp_all [toSource,rename,ZFR.rename,lift_eq]
@[simp] theorem toSource_shift (p:Formula) : toSource (shift p)=ZFR.shift (toSource p) :=
 toSource_rename Nat.succ p
@[simp] theorem toSource_subst (n:Nat)(p:Formula) : toSource (subst n p)=ZFR.subst n (toSource p) := by
 simpa only [subst,ZFR.subst,substMap_eq] using toSource_rename (substMap n) p
@[simp] theorem toSource_bound (p:Formula)(n:Nat) : ZFR.Bound (toSource p) n ↔ Bound p n := by
 induction p generalizing n <;> simp_all [toSource,Bound,ZFR.Bound]
def toSourceContext (Γ:Context):ZFR.Context := Γ.map toSource
def toSourceRow : Row → ZFR.Row
 | .seq Γ p => .seq (toSourceContext Γ) (toSource p)
 | .branches Γ a b c => .branches (toSourceContext Γ) (toSource a) (toSource b) (toSource c)
@[simp] theorem toSourceContext_shift (Γ:Context) :
 toSourceContext (shiftContext Γ)=ZFR.shiftContext (toSourceContext Γ) := by
 simp only [toSourceContext,shiftContext,ZFR.shiftContext,List.map_map]
 apply List.map_congr_left; intro a _; exact toSource_shift a
theorem toSource_contextSub {Γ Δ:Context} (h:ContextSub Γ Δ):
 ZFR.ContextSub (toSourceContext Γ) (toSourceContext Δ) := by
 intro a ha
 obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
 exact List.mem_map.mpr ⟨b,h b hb,rfl⟩
theorem toSource_nd {r:Row} (h:ND r):ZFR.ND (toSourceRow r) := by
 induction h with
 | ctx hm => exact ZFR.ND.ctx (List.mem_map.mpr ⟨_,hm,rfl⟩)
 | pc Γ a b => exact ZFR.ND.pc _ _ _
 | ii h ih => exact ZFR.ND.ii ih
 | ie h1 h2 ih1 ih2 => exact ZFR.ND.ie ih1 ih2
 | exp h ih => exact ZFR.ND.exp ih
 | ci h1 h2 ih1 ih2 => exact ZFR.ND.ci ih1 ih2
 | ce1 h ih => exact ZFR.ND.ce1 ih
 | ce2 h ih => exact ZFR.ND.ce2 ih
 | di1 h ih => exact ZFR.ND.di1 ih
 | di2 h ih => exact ZFR.ND.di2 ih
 | branchPair h1 h2 ih1 ih2 => exact ZFR.ND.branchPair ih1 ih2
 | de h1 h2 ih1 ih2 => exact ZFR.ND.de ih1 ih2
 | wk hs h ih => exact ZFR.ND.wk (toSource_contextSub hs) ih
 | allI h ih =>
   apply ZFR.ND.allI
   simpa only [toSourceRow,toSourceContext_shift] using ih
 | allE t h ih =>
   simpa only [toSourceRow,toSource,toSource_subst] using ZFR.ND.allE t ih
 | exI t h ih =>
   apply ZFR.ND.exI t
   simpa only [toSourceRow,toSource_subst] using ih
 | exE h1 h2 ih1 ih2 =>
   apply ZFR.ND.exE ih1
   simpa only [toSourceRow,toSourceContext,shiftContext,ZFR.shiftContext,List.map_cons,List.map_map,Function.comp_def,toSource_shift] using ih2
@[simp] theorem ofSource_rename (σ:Nat→Nat)(p:ZFR.Formula) :
 ofSource (ZFR.rename σ p)=rename σ (ofSource p) := by
 induction p generalizing σ <;> simp_all [ofSource,rename,ZFR.rename,lift_eq]
@[simp] theorem ofSource_shift (p:ZFR.Formula) : ofSource (ZFR.shift p)=shift (ofSource p) :=
 ofSource_rename Nat.succ p
@[simp] theorem ofSource_subst (n:Nat)(p:ZFR.Formula) : ofSource (ZFR.subst n p)=subst n (ofSource p) := by
 simpa only [subst,ZFR.subst,substMap_eq] using ofSource_rename (ZFR.substMap n) p
@[simp] theorem ofSource_bound (p:ZFR.Formula)(n:Nat) : Bound (ofSource p) n ↔ ZFR.Bound p n := by
 induction p generalizing n <;> simp_all [ofSource,Bound,ZFR.Bound]
def ofSourceContext (Γ:ZFR.Context):Context := Γ.map ofSource
def ofSourceRow : ZFR.Row → Row
 | .seq Γ p => .seq (ofSourceContext Γ) (ofSource p)
 | .branches Γ a b c => .branches (ofSourceContext Γ) (ofSource a) (ofSource b) (ofSource c)
@[simp] theorem ofSourceContext_shift (Γ:ZFR.Context) :
 ofSourceContext (ZFR.shiftContext Γ)=shiftContext (ofSourceContext Γ) := by
 simp only [ofSourceContext,shiftContext,ZFR.shiftContext,List.map_map]
 apply List.map_congr_left; intro a _; exact ofSource_shift a
theorem ofSource_contextSub {Γ Δ:ZFR.Context} (h:ZFR.ContextSub Γ Δ):
 ContextSub (ofSourceContext Γ) (ofSourceContext Δ) := by
 intro a ha
 obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
 exact List.mem_map.mpr ⟨b,h b hb,rfl⟩
theorem ofSource_nd {r:ZFR.Row} (h:ZFR.ND r):ND (ofSourceRow r) := by
 induction h with
 | ctx hm => exact ND.ctx (List.mem_map.mpr ⟨_,hm,rfl⟩)
 | pc Γ a b => exact ND.pc _ _ _
 | ii h ih => exact ND.ii ih
 | ie h1 h2 ih1 ih2 => exact ND.ie ih1 ih2
 | exp h ih => exact ND.exp ih
 | ci h1 h2 ih1 ih2 => exact ND.ci ih1 ih2
 | ce1 h ih => exact ND.ce1 ih
 | ce2 h ih => exact ND.ce2 ih
 | di1 h ih => exact ND.di1 ih
 | di2 h ih => exact ND.di2 ih
 | branchPair h1 h2 ih1 ih2 => exact ND.branchPair ih1 ih2
 | de h1 h2 ih1 ih2 => exact ND.de ih1 ih2
 | wk hs h ih => exact ND.wk (ofSource_contextSub hs) ih
 | allI h ih =>
   apply ND.allI
   simpa only [ofSourceRow,ofSourceContext_shift] using ih
 | allE t h ih =>
   simpa only [ofSourceRow,ofSource,ofSource_subst] using ND.allE t ih
 | exI t h ih =>
   apply ND.exI t
   simpa only [ofSourceRow,ofSource_subst] using ih
 | exE h1 h2 ih1 ih2 =>
   apply ND.exE ih1
   simpa only [ofSourceRow,ofSourceContext,shiftContext,ZFR.shiftContext,List.map_cons,List.map_map,Function.comp_def,ofSource_shift] using ih2
@[simp] theorem ofSourceContext_toSourceContext (Γ:Context):
 ofSourceContext (toSourceContext Γ)=Γ := by
 simp [ofSourceContext,toSourceContext,List.map_map,Function.comp_def]
@[simp] theorem ofSourceRow_toSourceRow (r:Row):ofSourceRow (toSourceRow r)=r := by
 cases r <;> simp [ofSourceRow,toSourceRow]
end PalomarZF209
