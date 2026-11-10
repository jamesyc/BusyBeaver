import PA215.Source.CachedV2.SelectedOriginal
import PA215.OriginalHaltCertified
import PA215.OriginalTerminalMetadata
set_option maxRecDepth 100000
namespace PA215.Source.CachedV2
open PA215.Runtime PA215.Census
attribute [local irreducible] exactSites originalAt PA215.Census.all

theorem halt_original_target (ha : agreesWith s r = true) (hh : s.op = .halt) :
    r.target = none := by
  cases ht : r.target with
  | none => rfl
  | some t =>
    cases hb : r.branch <;> simp [agreesWith,targetPlan,hh,hb,ht] at ha

/-- The unique original terminal certificate handles the explicit source halt
with the unchanged full root frame and actual physical file. -/
theorem terminal_primitive
    (hterminal : OriginalHaltCertified ⟨5114,by decide⟩)
    (i : Nat) (s : Site) (n : Nat) (vs : List Nat)
    (hs : exactSites[i]? = some s) (hh : s.op = .halt) (hv : 10 ≤ vs.length) :
    PA215.Zip.Halts PA215.NativeTable.machine (conc n vs (rootFrame s.path)) := by
  obtain ⟨j,hi,hvalid,ha⟩ := selected_original i s vs hs hv
  have ht := halt_original_target ha hh
  have hj : j = (⟨5114,by decide⟩ : Fin 5134) := Fin.ext ((originalAt_target_none_iff j).mp ht)
  subst j
  have hr := hterminal.sound n vs hvalid
  rw [agrees_initial ha n vs] at hr
  exact hr
#print axioms terminal_primitive
end PA215.Source.CachedV2
