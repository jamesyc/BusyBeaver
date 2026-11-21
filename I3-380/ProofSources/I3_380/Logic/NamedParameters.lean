module
public import I3_380.Logic.Expanded
public import I3_380.SquareSchemas
@[expose] public section

namespace PalomarI3380.Logic.Expanded

variable {V : Type}

def Argument.names : Argument V → List V
  | .variable _ => []
  | .named x => [x]

def Formula.names : Formula V → List V
  | .bot => []
  | .eq x y | .mem x y | .order x y => x.names ++ y.names
  | .and p q | .or p q | .imp p q => p.names ++ q.names
  | .all p | .ex p => p.names

def Argument.lower (slot : V → Nat) (n : Nat) : Argument V → Nat
  | .variable i => i
  | .named v => n + slot v

/-- Place the finitely many names in parameter slots above the live
variables. This translation interprets the extra order as empty. -/
def Formula.lower (slot : V → Nat) (n : Nat) : Formula V → Logic.Formula
  | .bot => .bot
  | .eq x y => .eq (x.lower slot n) (y.lower slot n)
  | .mem x y => .mem (x.lower slot n) (y.lower slot n)
  | .order _ _ => .bot
  | .and p q => .and (p.lower slot n) (q.lower slot n)
  | .or p q => .or (p.lower slot n) (q.lower slot n)
  | .imp p q => .imp (p.lower slot n) (q.lower slot n)
  | .all p => .all (p.lower slot (n + 1))
  | .ex p => .ex (p.lower slot (n + 1))

private theorem argument_scope {slot : V → Nat} {n m : Nat} {x : Argument V}
    (h : x.bound n) (places : ∀v ∈ x.names, slot v < m) : x.lower slot n < m + n := by
  cases x with
  | «variable» i => exact Nat.lt_of_lt_of_le h (Nat.le_add_left _ _)
  | named v =>
    have chosen := places v (List.mem_singleton.mpr rfl)
    change n + slot v < m + n
    omega

theorem lower_scope (slot : V → Nat) (p : Formula V) {n m : Nat}
    (h : Bound p n) (places : ∀v ∈ p.names, slot v < m) : Logic.Bound (p.lower slot n) (m + n) := by
  induction p generalizing n with
  | bot | order => trivial
  | eq x y | mem x y =>
    exact ⟨argument_scope h.1 (fun v hm => places v (List.mem_append_left _ hm)),
      argument_scope h.2 (fun v hm => places v (List.mem_append_right _ hm))⟩
  | and p q ihp ihq | or p q ihp ihq | imp p q ihp ihq =>
    exact ⟨ihp h.1 (fun v hm => places v (List.mem_append_left _ hm)),
      ihq h.2 (fun v hm => places v (List.mem_append_right _ hm))⟩
  | all p ih | ex p ih =>
    exact ih h places

private theorem argument_value {slot : V → Nat} {n : Nat} {x : Argument V} {orig translated : Nat → V}
    (h : x.bound n) (variables : ∀ i, i < n → translated i = orig i)
    (names : ∀ v ∈ x.names, translated (n + slot v) = v) :
    translated (x.lower slot n) = x.value orig := by
  cases x with
  | «variable» i => exact variables i h
  | named v => exact names v (List.mem_singleton.mpr rfl)

theorem lower_eval (E : V → V → Prop) (slot : V → Nat) (p : Formula V) {n : Nat}
    (h : Bound p n) (orig translated : Nat → V)
    (variables : ∀ i, i < n → translated i = orig i)
    (names : ∀ v ∈ p.names, translated (n + slot v) = v) :
    Logic.eval E (p.lower slot n) translated ↔ eval E (fun _ _ => False) p orig := by
  induction p generalizing n orig translated with
  | bot | order => exact Iff.rfl
  | eq x y | mem x y =>
    have first := argument_value h.1 variables (fun v hm => names v (List.mem_append_left _ hm))
    have second := argument_value h.2 variables (fun v hm => names v (List.mem_append_right _ hm))
    simp only [Formula.lower, Logic.eval, eval, first, second]
  | and p q ip iq | or p q ip iq | imp p q ip iq =>
    have first := ip h.1 orig translated variables (fun v hm => names v (List.mem_append_left _ hm))
    have next := iq h.2 orig translated variables (fun v hm => names v (List.mem_append_right _ hm))
    simp only [Formula.lower, Logic.eval, eval, first, next]
  | all p ih =>
    apply forall_congr'
    intro x
    apply ih h
    · intro i hi
      cases i with
      | zero => rfl
      | succ i => exact variables i (by omega)
    · intro v hm
      rw [show n + 1 + slot v = n + slot v + 1 by omega]
      exact names v hm
  | ex p ih =>
    apply exists_congr
    intro x
    apply ih h
    · intro i hi
      cases i with
      | zero => rfl
      | succ i => exact variables i (by omega)
    · intro v hm
      rw [show n + 1 + slot v = n + slot v + 1 by omega]
      exact names v hm

noncomputable def slot (names : List V) (x : V) : Nat := by
  classical
  exact if h : x ∈ names then Classical.choose (List.mem_iff_getElem.mp h) else 0

theorem slot_value {names : List V} {x : V} (h : x ∈ names) :
    ∃ inside : slot names x < names.length, names[slot names x]'inside = x := by
  unfold slot
  rw [dite_eq_left h]
  exact Classical.choose_spec (List.mem_iff_getElem.mp h)

private def extra (names : List V) (default : V) : Nat → V :=
  fun i => names[i]?.getD default

theorem lower_binary (E : V → V → Prop) {R : V → V → Prop}
    (definition : Binary E (fun _ _ => False) R) (default : V) :
    ∃ (n : Nat) (φ : Logic.Formula) (constants : Nat → V),
      Logic.Bound φ (n + 2) ∧ ∀ x y,
        Logic.eval E φ (pushValue (pushValue constants y) x) ↔ R x y := by
  obtain ⟨p, scope, meaning⟩ := definition
  let names := p.names
  let extraValues := extra names default
  refine ⟨names.length, p.lower (slot names) 2, extraValues, ?_, fun x y => ?_⟩
  · exact lower_scope (slot names) p scope (fun _ present => (slot_value present).choose)
  · let assignment := pushValue (pushValue extraValues y) x
    refine (lower_eval E (slot names) p scope assignment assignment (fun _ _ => rfl) ?_).trans
      (meaning assignment)
    intro v hv
    obtain ⟨inside, get⟩ := slot_value hv
    rw [show 2 + slot names v = slot names v + 1 + 1 by omega]
    change names[slot names v]?.getD default = v
    rw [List.getElem?_eq_getElem inside, get]
    rfl

end PalomarI3380.Logic.Expanded
