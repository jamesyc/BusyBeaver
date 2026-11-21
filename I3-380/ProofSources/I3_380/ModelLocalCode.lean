module
public import I3_380.LocalFormulas
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

noncomputable def rowValue (r : LocalFormula.Row) : V :=
  N.orderedPair (N.numeral r.tag) (N.orderedPair (N.numeral r.first) (N.numeral r.second))

noncomputable def syntaxGraph (rows : List LocalFormula.Row) : V :=
  N.listGraph (rows.map N.rowValue)

theorem syntaxGraph_at (rows : List LocalFormula.Row) {i : Nat} (bound : i < rows.length) :
    Internal.RowAt N.mem (N.syntaxGraph rows) (N.numeral i) (N.numeral rows[i].tag)
      (N.numeral rows[i].first) (N.numeral rows[i].second) := by
  let sep := rows[i]
  let first := N.numeral sep.first
  let second := N.numeral sep.second
  let tag := N.numeral sep.tag
  let params := N.orderedPair first second
  let value := N.orderedPair tag params
  have graph : Internal.At N.mem (N.syntaxGraph rows) (N.numeral i) value := by
    change Internal.At N.mem (N.listGraph (rows.map N.rowValue)) _ _
    have within : i < (rows.map N.rowValue).length := by simpa only [List.length_map] using bound
    refine (N.listGraph_value _ _ _).mpr ⟨⟨i,within⟩,rfl,?_⟩
    simp only [List.getElem_map]
    rfl
  exact ⟨value,params,graph,N.orderedPair_intro _ _,N.orderedPair_intro _ _⟩

theorem row_valid_in_model {r : LocalFormula.Row} {i : Nat} (ready : r.validAt i) :
    Internal.ValidRow N.mem (N.numeral 3) (N.numeral i) (N.numeral r.tag)
      (N.numeral r.first) (N.numeral r.second) := by
  have nm {a b : Nat} (h : a < b) : N.mem (N.numeral a) (N.numeral b) :=
    (N.mem_numeral _ _).mpr ⟨a,h,rfl⟩
  have literal {t : Nat} (eq : r.tag = t) : Internal.Numeral N.mem t (N.numeral r.tag) :=
    (N.numeral_def _ _).mpr (congrArg N.numeral eq)
  rcases ready with ⟨tag,a,b⟩ | ⟨tag,a,b⟩ | ⟨tag,a⟩ | ⟨tag,a,b⟩ | ⟨tag,a,b⟩
  · exact Or.inl ⟨literal tag,nm a,nm b⟩
  · exact Or.inr (Or.inl ⟨literal tag,nm a,nm b⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨literal tag,nm a⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨literal tag,nm a,nm b⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨literal tag,nm a,nm b⟩)))

theorem syntaxGraph_code {w : V} (omega : Internal.Omega N.mem w) (rows : List LocalFormula.Row)
    (nonempty : 0 < rows.length) (valid : LocalFormula.WellFormed rows) :
    Internal.SyntaxCode N.mem w (N.numeral 3) (N.numeral rows.length) (N.syntaxGraph rows) := by
  have window : ¬Internal.Empty N.mem (N.numeral rows.length) :=
    fun no => no _ ((N.mem_numeral _ _).mpr ⟨0,nonempty,rfl⟩)
  have graph : Internal.FunctionOn N.mem (N.syntaxGraph rows) (N.numeral rows.length) := by
    simpa only [syntaxGraph,List.length_map] using N.listGraph_function (rows.map N.rowValue)
  refine ⟨N.numeral_in_omega omega 3,N.numeral_in_omega omega _,window,graph,fun i hi => ?_⟩
  obtain ⟨j,inside,eq⟩ := (N.mem_numeral _ _).mp hi
  subst i
  exact ⟨N.numeral rows[j].tag,N.numeral rows[j].first,N.numeral rows[j].second,
    N.syntaxGraph_at rows inside,N.numeral_in_omega omega _,N.numeral_in_omega omega _,
    N.row_valid_in_model (valid j inside)⟩

def ReadsAssignment (env : V) (values : Fin 3 → V) : Prop :=
  ∀ i, Internal.At N.mem env (N.numeral i.val) (values i)

theorem assignment_values {stage env : V} (typed : Internal.FunctionInto N.mem env (N.numeral 3) stage) :
    ∃ values : Fin 3 → V, N.ReadsAssignment env values ∧ ∀ i, N.mem (values i) stage := by
  have candidates (i : Fin 3) : ∃ x, Internal.At N.mem env (N.numeral i.val) x := by
    obtain ⟨x,hx,_⟩ := typed.1.1 (N.numeral i.val) ((N.mem_numeral _ _).mpr ⟨i.val,i.isLt,rfl⟩)
    exact ⟨x,hx⟩
  let values := fun i => Classical.choose (candidates i)
  have reads : N.ReadsAssignment env values := fun i => Classical.choose_spec (candidates i)
  exact ⟨values,reads,fun i => typed.2 _ ((N.mem_numeral _ _).mpr ⟨i.val,i.isLt,rfl⟩) _ (reads i)⟩

theorem assignment_at_iff {s env : V} {values : Fin 3 → V}
    (typed : Internal.FunctionInto N.mem env (N.numeral 3) s) (reads : N.ReadsAssignment env values)
    (i : Fin 3) (x : V) : Internal.At N.mem env (N.numeral i.val) x ↔ x = values i := by
  obtain ⟨k,_,one⟩ := typed.1.1 (N.numeral i.val) ((N.mem_numeral _ _).mpr ⟨i.val,i.isLt,rfl⟩)
  exact ⟨fun h => (one x h).trans (one (values i) (reads i)).symm,fun h => h.symm ▸ reads i⟩

theorem assignment_realize {stage : V} (values : Fin 3 → V) (bounded : ∀ i, N.mem (values i) stage) :
    ∃ env, Internal.FunctionInto N.mem env (N.numeral 3) stage ∧ N.ReadsAssignment env values := by
  let list := List.ofFn values
  have length : list.length = 3 := List.length_ofFn
  have covers : ∀ x ∈ list, N.mem x stage := by
    intro x hx
    obtain ⟨i,found⟩ := List.mem_ofFn.mp hx
    exact found ▸ bounded i
  refine ⟨N.listGraph list,by simpa only [length] using N.listGraph_into list stage covers,fun i => ?_⟩
  have li : i.val < list.length := by simpa only [length] using i.isLt
  refine (N.listGraph_value _ _ _).mpr ⟨⟨i.val, li⟩,rfl,?_⟩
  change values i = (List.ofFn values)[i.val]
  rw [List.getElem_ofFn]

theorem assignments_agree {stage a b : V} {v u : Fin 3 → V}
    (ha : Internal.FunctionInto N.mem a (N.numeral 3) stage) (hb : Internal.FunctionInto N.mem b (N.numeral 3) stage)
    (valueA : N.ReadsAssignment a v) (valueB : N.ReadsAssignment b u) (i : Fin 3) :
    Internal.AgreesAway N.mem (N.numeral 3) a b (N.numeral i.val) ↔
      ∀ j, j ≠ i → v j = u j := by
  constructor
  · intro h j different
    have symbol : N.numeral j.val ≠ N.numeral i.val := fun eq => different (Fin.ext (N.numeral_injective eq))
    have yes := (h _ ((N.mem_numeral _ _).mpr ⟨j.val,j.isLt,rfl⟩) symbol (v j)).mp (valueA j)
    exact (N.assignment_at_iff hb valueB j _).mp yes
  · intro h j member distinct x
    obtain ⟨n,hn,same⟩ := (N.mem_numeral _ _).mp member
    subst j
    let k : Fin 3 := ⟨n,hn⟩
    have different : k ≠ i := fun eq => distinct (congrArg (fun j : Fin 3 => N.numeral j.val) eq)
    exact (N.assignment_at_iff ha valueA k x).trans
      ((Iff.of_eq (congrArg (x = ·) (h k different))).trans (N.assignment_at_iff hb valueB k x).symm)

end PalomarI3380.SquareRepresentation.SetContext
