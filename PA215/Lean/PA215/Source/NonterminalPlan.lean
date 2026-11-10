import PA215.Source.ContractPlan
namespace PA215.Source
open PA215.Runtime

private theorem bind_double_some_ne (o : Option α) (f : α → β) :
    o.bind (fun x => some (some (f x))) ≠ some none := by
  cases o <;> simp

theorem terminal_plan_halt (s : Site) (br : Branch)
    (hp : targetPlan s br = some none) : s.op = .halt := by
  cases s with
  | mk path op =>
    cases op <;> cases br with
    | none => simp_all [targetPlan,bind_double_some_ne]
    | some p =>
      rcases p with ⟨r,z⟩
      cases z <;> simp_all [targetPlan,bind_double_some_ne]

/-- A non-halt source operation whose original full frame agrees must have
an actual nonterminal original target. -/
theorem nonhalt_original_target (ha : agreesWith s r = true) (hh : s.op ≠ .halt) :
    ∃ t, r.target = some t := by
  cases ht : r.target with
  | some t => exact ⟨t,rfl⟩
  | none =>
    have hp : targetPlan s r.branch = some none := by
      cases he : targetPlan s r.branch with
      | none => simp [agreesWith,he] at ha
      | some p =>
        cases p with
        | none => rfl
        | some p => simp [agreesWith,he,ht] at ha
    exact False.elim (hh (terminal_plan_halt s r.branch hp))
#print axioms nonhalt_original_target
end PA215.Source
