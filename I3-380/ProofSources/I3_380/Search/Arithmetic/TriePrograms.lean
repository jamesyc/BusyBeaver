module
public import I3_380.Search.Compiler.Trie
public import I3_380.Search.Arithmetic.ModelPatterns
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceCantor (pairValue decodeLeft decodeRight decode_pairValue)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem ClearScratch.controls {V : Type} [OfNat V 0] {s : Store V} (h : ClearScratch s) (p r : V) :
    ClearScratch (controls s p r) := (h.setPL p).setSel r

theorem replaceContext_controls (s : Store M) (p r a b g : M) :
    replaceContext (controls s p r) a b g = controls (replaceContext s a b g) p r := by
  funext x
  by_cases f : x = fr <;> by_cases l : x = lv <;> by_cases m : x = gues <;>
    simp_all [replaceContext,controls,Store.set,fr,lv,gues,pl,sel] <;> rfl

theorem controlledContext_merge (s : Store M) (p v a b g p' v' a' b' g' : M) :
    controls (replaceContext (controls (replaceContext s a b g) p v) a' b' g') p' v' =
      controls (replaceContext s a' b' g') p' v' := by
  rw [replaceContext_controls,controls_override,replaceContext_replace]

theorem controls_pl {V : Type} (s : Store V) (pending selector : V) :
    controls s pending selector pl = pending := by simp [controls,Store.set,pl,sel]

theorem controls_sel {V : Type} (s : Store V) (pending selector : V) :
    controls s pending selector sel = selector := Store.get_set ..

theorem replaceContext_pl (s : Store M) (a b g : M) :
    replaceContext s a b g pl = s pl := by simp [replaceContext,Store.set,pl,fr,lv,gues]

def CodedTrieOutcome (ps : List Program) (s : Store M) : Prop :=
  ∃ a b g p r : M, p ≤ s pl ∧ CodedLines ps s.code (controls (replaceContext s a b g) p r).code

theorem CodedTrieOutcome.patterns (row : List Pattern) (s : Store M) (ready : ClearScratch s) :
    CodedTrieOutcome (row.map Pattern.compile) s := by
  obtain ⟨a,b,g,line⟩ := coded_patterns row s ready
  have selector : replaceContext s a b g sel = s sel := by
    simp [replaceContext,Store.set,fr,lv,gues,sel]
  refine ⟨a,b,g,s pl,s sel,le_rfl,?_⟩
  rwa [← replaceContext_pl s a b g,← selector,controls_same]

theorem CodedTrieOutcome.prefix {ps : List Program} (pat : Pattern) (s : Store M) (ready : ClearScratch s)
    (tail : ∀ t : Store M, ClearScratch t → CodedTrieOutcome ps t) :
    CodedTrieOutcome (pat.compile :: ps) s := by
  obtain ⟨a,b,g,head⟩ := coded_pattern pat s ready
  obtain ⟨a',b',g',p,r,bound,rest⟩ := tail _ (ready.context_state a b g)
  rw [replaceContext_pl] at bound
  rw [replaceContext_replace] at rest
  exact ⟨a',b',g',p,r,bound,.cons head rest⟩

theorem coded_choose (branch : Option Pattern → List Program) (keys : List (Option Pattern))
    (s : Store M) (ready : ClearScratch s)
    (exec : ∀ k ∈ keys, ∀ t : Store M, ClearScratch t → CodedTrieOutcome (branch k) t) :
    CodedTrieOutcome (chooseBranches branch keys) s := by
  rcases keys with _ | ⟨k,_ | ⟨l,ks⟩⟩
  · exact CodedTrieOutcome.patterns [] s ready
  · exact exec k (by simp) s ready
  let keys := k :: l :: ks
  let front := decodeLeft (s pl)
  let pending := decodeRight (s pl)
  let next := controls s pending (s sel+front)
  have loaded : (read sel).Runs .normal s.code next.code :=
    coded_read (by decide) (by decide) s ready.tokZero ready.auxZero
  obtain ⟨chosen,residual,member,selection⟩ := modelSelect_exists (ps := keys) (by simp [keys]) (next sel)
  let start := controls s pending residual
  obtain ⟨a,b,g,p,r,bound,line⟩ := exec chosen member start (ready.controls _ _)
  have chosenProgram := modelSelect_map (fun key => block (branch key)) keys (next sel)
  rw [selection] at chosenProgram
  have run : (block (branch chosen)).Runs .normal (next.set sel residual).code
      (controls (replaceContext s a b g) p r).code := by
    rw [show next.set sel residual = start from Store.set_set ..]
    rw [replaceContext_controls,controls_override] at line
    exact line.block
  have dispatched := coded_dispatch _ next chosenProgram run
  have pendingLe : pending ≤ s pl := by
    change decodeRight (s pl) ≤ s pl
    exact (ArithmeticMachine.SourceCantor.decodeValue_bounds _).2
  rw [show start pl = pending from controls_pl ..] at bound
  exact ⟨a,b,g,p,r,bound.trans pendingLe,.cons loaded (.cons dispatched (.nil _))⟩

theorem coded_trie (fuel : Nat) (rows : List (List Pattern)) (nonempty : rows ≠ [])
    (adequate : ∀ row ∈ rows, row.length ≤ fuel) (s : Store M) (ready : ClearScratch s) :
    CodedTrieOutcome (trie fuel rows) s := by
  induction fuel generalizing rows s with
  | zero =>
    cases rows with
    | nil => exact (nonempty rfl).elim
    | cons row more =>
      have empty : row = [] := by simpa using adequate row List.mem_cons_self
      subst row
      exact CodedTrieOutcome.patterns [] s ready
  | succ fuel ih =>
    rcases rows with _ | ⟨first,_ | ⟨second,more⟩⟩
    · exact (nonempty rfl).elim
    · exact CodedTrieOutcome.patterns first s ready
    apply coded_choose _ _ s ready
    intro key belongs t h
    cases key with
    | none => exact CodedTrieOutcome.patterns [] t h
    | some pattern =>
      have enough : ∀ row ∈ branchTail (some pattern) (first :: second :: more), row.length ≤ fuel := by
        intro row member
        have bound := adequate _ (branchTail_mem.mp member)
        simpa only [List.length_cons,Nat.add_le_add_iff_right] using bound
      exact CodedTrieOutcome.prefix pattern t h (fun endState h' => ih _ (eligible_tail belongs) enough endState h')

theorem coded_rows (s : Store M) (ready : ClearScratch s) :
    CodedTrieOutcome compiledRows s :=
  coded_trie _ _ (by decide) (foldMaximum _ 0).2 s ready

end PalomarI3380.Compiler.Source
