module
public import I3_380.ModelLocalCode
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

private theorem eval_row {w rows stage sat env : V} {full before tail : List LocalFormula.Row} {r : LocalFormula.Row}
    (encoded : rows = N.syntaxGraph full) (shape : full = before ++ r :: tail)
    (code : Internal.SyntaxCode N.mem w (N.numeral 3) (N.numeral full.length) rows)
    (table : Internal.TruthSet N.mem (N.numeral 3) (N.numeral full.length) rows stage sat)
    (typed : Internal.FunctionInto N.mem env (N.numeral 3) stage) :
    Internal.At N.mem sat (N.numeral before.length) env ↔
      Internal.RowTruth N.mem (Internal.At N.mem sat) (N.numeral 3) stage env
        (N.numeral r.tag) (N.numeral r.first) (N.numeral r.second) := by
  subst rows
  have inside : before.length < full.length := by rw [shape]; simp
  have atIndex : full[before.length] = r := by
    have hit : full[before.length]? = some r := by
      rw [shape,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero]
    simpa only [List.getElem?_eq_getElem inside,Option.some.injEq] using hit
  have got := N.syntaxGraph_at full inside
  rw [atIndex] at got
  exact N.truthSet_rule code table ((N.mem_numeral _ _).mpr ⟨before.length,inside,rfl⟩) typed got

set_option maxHeartbeats 3500000 in
/-- The set-coded Tarski recursion agrees with ordinary three-variable
evaluation on each compiled finite formula. The proof works for any
truth graph satisfying the model's clauses. -/
theorem eval_emitted {w stage sat : V} {full : List LocalFormula.Row}
    (code : Internal.SyntaxCode N.mem w (N.numeral 3) (N.numeral full.length) (N.syntaxGraph full))
    (table : Internal.TruthSet N.mem (N.numeral 3) (N.numeral full.length) (N.syntaxGraph full) stage sat)
    (formula : LocalFormula) (base tail : List LocalFormula.Row) (shape : full = formula.emit base ++ tail)
    {env : V} (typed : Internal.FunctionInto N.mem env (N.numeral 3) stage)
    {values : Fin 3 → V} (reads : N.ReadsAssignment env values) :
    Internal.At N.mem sat (N.numeral ((formula.emit base).length - 1)) env ↔
      LocalFormula.eval N.mem (fun x => N.mem x stage) formula values := by
  have tags (a b : Nat) : N.numeral a = N.numeral b ↔ a = b :=
    ⟨fun h => N.numeral_injective h, congrArg N.numeral⟩
  induction formula generalizing base tail env values with
  | equal a b =>
    have h : full = base ++ ⟨0,a.val,b.val⟩ :: tail := by
      simpa only [LocalFormula.emit,LocalFormula.appendRow,List.append_assoc,List.singleton_append] using shape
    have decoded := N.eval_row rfl h code table typed
    simp [ Internal.RowTruth, N.numeral_def, tags] at decoded
    simpa [LocalFormula.emit,LocalFormula.appendRow,LocalFormula.eval,Internal.AtomicTruth,
      N.assignment_at_iff typed reads a,N.assignment_at_iff typed reads b] using decoded
  | member a b =>
    have h : full = base ++ ⟨1,a.val,b.val⟩ :: tail := by
      simpa only [LocalFormula.emit,LocalFormula.appendRow,List.append_assoc,List.singleton_append] using shape
    have decoded := N.eval_row rfl h code table typed
    simp [ Internal.RowTruth, N.numeral_def, tags] at decoded
    simpa [LocalFormula.emit,LocalFormula.appendRow,LocalFormula.eval,Internal.AtomicTruth,
      N.assignment_at_iff typed reads a,N.assignment_at_iff typed reads b] using decoded
  | neg p ih =>
    let previous := p.emit base
    let line : LocalFormula.Row := ⟨2, previous.length - 1, 0⟩
    have h : full = previous ++ line :: tail := by
      simpa only [LocalFormula.emit,LocalFormula.appendRow,List.append_assoc,List.singleton_append] using shape
    have raw := N.eval_row rfl h code table typed
    have root : ((LocalFormula.neg p).emit base).length - 1 = previous.length := by
      simp [LocalFormula.emit,LocalFormula.appendRow,previous]
    rw [root]
    simp [line, Internal.RowTruth, N.numeral_def, tags] at raw
    exact raw.trans (not_congr (ih base (line :: tail) h typed reads))
  | conj p q ip iq =>
    let first := p.emit base
    let second := q.emit first
    let line : LocalFormula.Row := ⟨3, first.length - 1, second.length - 1⟩
    have h : full = second ++ line :: tail := by
      simpa only [LocalFormula.emit,LocalFormula.appendRow,List.append_assoc,List.singleton_append] using shape
    have raw := N.eval_row rfl h code table typed
    have root : ((LocalFormula.conj p q).emit base).length - 1 = second.length := by
      simp [LocalFormula.emit,LocalFormula.appendRow,second,first]
    rw [root]
    obtain ⟨rest, extension, _⟩ := q.emit_extensions first
    have fromFirst : full = first ++ (rest ++ line :: tail) := by
      change full = (p.emit base) ++ (rest ++ line :: tail)
      rw [h]
      change (q.emit first) ++ line :: tail = _
      rw [extension,List.append_assoc]
    simp [line, Internal.RowTruth, N.numeral_def, tags] at raw
    exact raw.trans (and_congr (ip base (rest ++ line :: tail) fromFirst typed reads)
      (iq first (line :: tail) h typed reads))
  | bind i p ih =>
    let before := p.emit base
    let line : LocalFormula.Row := ⟨4,i.val,before.length - 1⟩
    have h : full = before ++ line :: tail := by
      simpa only [LocalFormula.emit,LocalFormula.appendRow,List.append_assoc,List.singleton_append] using shape
    have raw := N.eval_row rfl h code table typed
    have root : ((LocalFormula.bind i p).emit base).length - 1 = before.length := by
      simp [LocalFormula.emit,LocalFormula.appendRow,before]
    rw [root]
    simp [line, Internal.RowTruth, N.numeral_def, tags] at raw
    refine raw.trans ⟨?_,?_⟩
    · rintro ⟨chosen,available,agreement,truth⟩
      obtain ⟨newValues,readNew,bounded⟩ := N.assignment_values available
      have same := (N.assignments_agree typed available reads readNew i).mp agreement
      have update : newValues = LocalFormula.bindValue values i (newValues i) := by
        funext j
        by_cases hEq : j = i
        · simp [LocalFormula.bindValue,hEq]
        · simp [LocalFormula.bindValue,hEq,(same j hEq).symm]
      have check := (ih base (line :: tail) h available readNew).mp truth
      exact ⟨newValues i,bounded i,update ▸ check⟩
    · rintro ⟨x,inRank,truth⟩
      let amended := LocalFormula.bindValue values i x
      have region (j : Fin 3) : N.mem (amended j) stage := by
        by_cases same : j = i
        · simpa [amended,LocalFormula.bindValue,same] using inRank
        · have known := typed.2 _ ((N.mem_numeral _ _).mpr ⟨j.val,j.isLt,rfl⟩) _ (reads j)
          simpa [amended,LocalFormula.bindValue,same] using known
      obtain ⟨changed,valid,seen⟩ := N.assignment_realize amended region
      have agrees := (N.assignments_agree typed valid reads seen i).mpr
        (fun j h => by simp [amended,LocalFormula.bindValue,h])
      exact ⟨changed,valid,agrees,(ih base (line :: tail) h valid seen).mpr truth⟩

/-- A set-elementary embedding preserves each finite three-variable
definition. The proof builds its internal syntax and assignments
explicitly. -/
theorem embedding_preserves_local {w stage j : V} (omega : Internal.Omega N.mem w)
    (mapping : Internal.FunctionInto N.mem j stage stage)
    (elementary : Internal.ElementaryOnRank N.mem w stage j)
    (p : LocalFormula) (value mapped : Fin 3 → V)
    (inStage : ∀ i, N.mem (value i) stage)
    (agrees : ∀ i, Internal.At N.mem j (value i) (mapped i)) :
    LocalFormula.eval N.mem (fun x => N.mem x stage) p value ↔
      LocalFormula.eval N.mem (fun x => N.mem x stage) p mapped := by
  let rows := p.emit []
  have progress : 0 < rows.length := LocalFormula.emit_grows p []
  have valid := LocalFormula.emit_wellFormed p (base := []) (by intro i h; contradiction)
  have code := N.syntaxGraph_code omega rows progress valid
  obtain ⟨sat,table,preservation⟩ := elementary _ _ _ code
  have mappedIn (i : Fin 3) : N.mem (mapped i) stage := mapping.2 _ (inStage i) _ (agrees i)
  obtain ⟨source,good,reads⟩ := N.assignment_realize value inStage
  obtain ⟨target,good',reads'⟩ := N.assignment_realize mapped mappedIn
  have hMap : Internal.MappedAssignment N.mem (N.numeral 3) j source target := by
    intro i hi a b atSource atImage
    obtain ⟨k,hk,same⟩ := (N.mem_numeral _ _).mp hi
    subst i
    let index : Fin 3 := ⟨k,hk⟩
    have eq := (N.assignment_at_iff good reads index _).mp atSource
    subst a
    obtain ⟨_,_,one⟩ := mapping.1.1 (value index) (inStage index)
    have mate := (one b atImage).trans (one (mapped index) (agrees index)).symm
    exact (N.assignment_at_iff good' reads' index b).mpr mate
  have index : N.mem (N.numeral (rows.length - 1)) (N.numeral rows.length) :=
    (N.mem_numeral _ _).mpr ⟨rows.length - 1,by omega,rfl⟩
  have shape : rows = p.emit [] ++ [] := by simp [rows]
  have left := N.eval_emitted code table p [] [] shape good reads
  have right := N.eval_emitted code table p [] [] shape good' reads'
  exact left.symm.trans ((preservation _ index source target good good' hMap).trans right)

end PalomarI3380.SquareRepresentation.SetContext
