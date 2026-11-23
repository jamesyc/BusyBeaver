module
public import I3_334Support.SetTheory.Graphs.FiniteGraphs
public import I3_334Support.SetTheory.Classes.TruthSets
@[expose] public section

namespace PalomarI3380.Logic

/-- The three object variables needed by the relation constructor W.
Binding may reuse a variable, as in the model's syntax graph. -/
inductive LocalFormula where
  | equal (a b : Fin 3)
  | member (a b : Fin 3)
  | neg (body : LocalFormula)
  | conj (left right : LocalFormula)
  | bind (index : Fin 3) (body : LocalFormula)

namespace LocalFormula

def bindValue {V : Type} (s : Fin 3 → V) (index : Fin 3) (x : V) : Fin 3 → V :=
  fun i => if i = index then x else s i

def eval {V : Type} (E : V → V → Prop) (D : V → Prop) : LocalFormula → (Fin 3 → V) → Prop
  | .equal a b, s => s a = s b
  | .member a b, s => E (s a) (s b)
  | .neg a, s => ¬eval E D a s
  | .conj a b, s => eval E D a s ∧ eval E D b s
  | .bind i p, s => ∃ x, D x ∧ eval E D p (bindValue s i x)

structure Row where
  tag : Nat
  first : Nat
  second : Nat

def Row.validAt (r : Row) (index : Nat) : Prop :=
  (r.tag = 0 ∧ r.first < 3 ∧ r.second < 3) ∨
  (r.tag = 1 ∧ r.first < 3 ∧ r.second < 3) ∨
  (r.tag = 2 ∧ r.first < index) ∨
  (r.tag = 3 ∧ r.first < index ∧ r.second < index) ∨
  (r.tag = 4 ∧ r.first < 3 ∧ r.second < index)

def WellFormed (rows : List Row) : Prop :=
  ∀ i, (h : i < rows.length) → rows[i].validAt i

def appendRow (rows : List Row) (row : Row) : List Row := rows ++ [row]

theorem wellFormed_append {rows : List Row} {r : Row} (before : WellFormed rows)
    (next : r.validAt rows.length) : WellFormed (appendRow rows r) := by
  intro i bound
  change i < (rows ++ [r]).length at bound
  change (rows ++ [r])[i].validAt i
  by_cases earlier : i < rows.length
  · rw [List.getElem_append_left earlier]
    exact before i earlier
  · have current : i = rows.length := by simp at bound; omega
    subst i
    rw [List.getElem_append_right (Nat.le_refl _)]
    simpa using next

def emit : LocalFormula → List Row → List Row
  | .equal a b, rows => appendRow rows ⟨0,a.val,b.val⟩
  | .member a b, rows => appendRow rows ⟨1,a.val,b.val⟩
  | .neg p, rows =>
    let previous := emit p rows
    appendRow previous ⟨2,previous.length - 1,0⟩
  | .conj p q, rows =>
    let before := emit p rows
    let later := emit q before
    appendRow later ⟨3,before.length - 1,later.length - 1⟩
  | .bind i p, rows =>
    let previous := emit p rows
    appendRow previous ⟨4,i.val,previous.length - 1⟩

theorem emit_extensions (p : LocalFormula) (base : List Row) :
    ∃ later, p.emit base = base ++ later ∧ 0 < later.length := by
  induction p generalizing base with
  | equal a b => exact ⟨[⟨0,a.val,b.val⟩],rfl,by simp⟩
  | member a b => exact ⟨[⟨1,a.val,b.val⟩],rfl,by simp⟩
  | neg p ih =>
    obtain ⟨middle, previous, positive⟩ := ih base
    exact ⟨middle ++ [⟨2,(p.emit base).length - 1,0⟩],
      by simp [emit,appendRow,← List.append_assoc,← previous],by simp⟩
  | conj p q ip iq =>
    obtain ⟨early,first,_⟩ := ip base
    obtain ⟨late,second,_⟩ := iq (p.emit base)
    exact ⟨early ++ late ++ [⟨3,(p.emit base).length - 1,(q.emit (p.emit base)).length - 1⟩],
      by
        simp only [emit,appendRow]
        rw [second,first]
        simp only [List.append_assoc],by simp <;> omega⟩
  | bind i p ih =>
    obtain ⟨middle, previous, positive⟩ := ih base
    exact ⟨middle ++ [⟨4,i.val,(p.emit base).length - 1⟩],
      by simp [emit,appendRow,← List.append_assoc,← previous],by simp⟩

theorem emit_grows (p : LocalFormula) (base : List Row) : base.length < (p.emit base).length := by
  obtain ⟨later,eq,grows⟩ := emit_extensions p base
  simp only [eq,List.length_append]
  omega

theorem emit_wellFormed (p : LocalFormula) {base : List Row} (h : WellFormed base) : WellFormed (p.emit base) := by
  induction p generalizing base with
  | equal a b => exact wellFormed_append h (Or.inl ⟨rfl,a.isLt,b.isLt⟩)
  | member a b => exact wellFormed_append h (Or.inr (Or.inl ⟨rfl,a.isLt,b.isLt⟩))
  | neg p ih =>
    have hLen := emit_grows p base
    exact wellFormed_append (ih h) (Or.inr (Or.inr (Or.inl ⟨rfl,by dsimp only [Row.first,Row.second]; omega⟩)))
  | conj p q ip iq =>
    have first := emit_grows p base
    have second := emit_grows q (p.emit base)
    exact wellFormed_append (iq (ip h)) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,by dsimp only [Row.first,Row.second]; omega,by dsimp only [Row.first,Row.second]; omega⟩))))
  | bind i p ih =>
    have hLen := emit_grows p base
    exact wellFormed_append (ih h) (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,i.isLt,by dsimp only [Row.first,Row.second]; omega⟩))))

end LocalFormula
end PalomarI3380.Logic
