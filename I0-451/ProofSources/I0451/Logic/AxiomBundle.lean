module
public import I0451.Logic.ProofStore

/-! Semantics of the CXVG axiom bundle. The variables `a,b,c` are also
numeric formula operands. The freshness guard applies to the final
conjunction; the eight preceding heads are unconditionally logical. -/
@[expose] public section
namespace I0451.Logic

open M6.Source.Cantor

/-- The same axiom expressions can be written for numeric codes or a
symbolic register evaluator. -/
structure AxiomEncoding (α : Type) where
  imp : α → α → α
  mem : α → α → α
  all : α → α → α
  equal : α → α → α
  ex : α → α → α
  and : α → α → α

/- The syntax templates specialize directly to numeric operations in the
semantic proof. The symbolic audit uses the same expressions. -/
macro "cxvg_heads%" "(" ex:term ", " equal:term ", " imp:term ", " all:term ", " mem:term ", " a:term ", " b:term ", " c:term ", " x:term ")" : term =>
  `([$ex $a ($equal $a $b),
   $imp ($all $a ($imp $b $c)) ($imp ($all $a $b) ($all $a $c)),
   $imp ($equal $a $b) ($imp ($mem $c $a) ($mem $c $b)),
   $imp ($all $a ($all $b $c)) ($all $b ($all $a $c)),
   $imp ($equal $c $a) ($imp ($mem $c $b) ($mem $a $b)),
   $imp ($ex $a ($all $a $b)) $b,
   $imp ($equal $c $a) ($imp ($equal $c $b) ($equal $a $b)),
   $imp ($imp ($imp $c $x) $a) ($imp ($imp $a $c) ($imp $b $c))])

macro "cxvg_subset%" "(" all:term ", " imp:term ", " mem:term ", " bound:term ", " a:term ", " b:term ")" : term =>
  `($all $bound ($imp ($mem $bound $a) ($mem $bound $b)))

macro "cxvg_containerCode%" "(" ex:term ", " and:term ", " all:term ", " imp:term ", " mem:term ", " subset:term ", " a:term ", " b:term ", " c:term ")" : term =>
  `($ex $b ($and ($all $a ($imp ($mem $a $b)
    ($and ($ex $c ($and ($all $b ($imp ($subset $c $b $a) ($mem $b $c))) ($mem $c $b))) ($subset $c $a $b))))
    ($mem $c $b)))

macro "cxvg_extensionalityCode%" "(" imp:term ", " subset:term ", " equal:term ", " a:term ", " b:term ", " c:term ")" : term =>
  `($imp ($subset $c $a $b) ($imp ($subset $c $b $a) ($equal $a $b)))

macro "cxvg_collectionCode%" "(" ex:term ", " and:term ", " all:term ", " imp:term ", " mem:term ", " a:term ", " b:term ", " label:term ", " formula:term ")" : term =>
  `($ex $label ($and ($all $a ($imp ($mem $a $b) ($all $b ($imp $formula ($ex $b ($and $formula ($mem $b $label)))))))
    ($all $b ($imp ($mem $b $label) ($ex $a $formula)))))

macro "cxvg_bundle%" "(" and:term ", " containerCode:term ", " extensionalityCode:term ", " imp:term ", " mem:term ", " all:term ", " equal:term ", " collectionCode:term ", " a:term ", " b:term ", " c:term ")" : term =>
  `($and ($containerCode $a $b $c) ($and ($extensionalityCode $a $b $c)
    ($and ($and ($imp ($mem $a $b) ($all $c ($mem $a $b))) ($imp ($equal $a $b) ($all $c ($equal $a $b))))
      ($collectionCode $a $b $c))))

namespace AxiomEncoding

def heads (op : AxiomEncoding α) (a b c x : α) : List α :=
  cxvg_heads%(op.ex, op.equal, op.imp, op.all, op.mem, a, b, c, x)

def subset (op : AxiomEncoding α) (bound a b : α) : α :=
  cxvg_subset%(op.all, op.imp, op.mem, bound, a, b)

def containerCode (op : AxiomEncoding α) (a b c : α) : α :=
  cxvg_containerCode%(op.ex, op.and, op.all, op.imp, op.mem, op.subset, a, b, c)

def extensionalityCode (op : AxiomEncoding α) (a b c : α) : α :=
  cxvg_extensionalityCode%(op.imp, op.subset, op.equal, a, b, c)

def collectionCode (op : AxiomEncoding α) (a b c : α) : α :=
  cxvg_collectionCode%(op.ex, op.and, op.all, op.imp, op.mem, a, b, c, c)

def bundle (op : AxiomEncoding α) (a b c : α) : α :=
  cxvg_bundle%(op.and, op.containerCode, op.extensionalityCode, op.imp, op.mem, op.all, op.equal, op.collectionCode, a, b, c)

end AxiomEncoding

def heads (a b c x : Nat) : List Nat :=
  cxvg_heads%(ex, equal, imp, all, mem, a, b, c, x)

def subset (bound a b : Nat) : Nat :=
  cxvg_subset%(all, imp, mem, bound, a, b)

def containerCode (a b c : Nat) : Nat :=
  cxvg_containerCode%(ex, and, all, imp, mem, subset, a, b, c)

def extensionalityCode (a b c : Nat) : Nat :=
  cxvg_extensionalityCode%(imp, subset, equal, a, b, c)

def collectionCode (a b c : Nat) : Nat :=
  cxvg_collectionCode%(ex, and, all, imp, mem, a, b, c, c)

def bundle (a b c : Nat) : Nat :=
  cxvg_bundle%(and, containerCode, extensionalityCode, imp, mem, all, equal, collectionCode, a, b, c)

/-- The AX proof-store effect, with a universal generalization and eight
logical heads saved on the stack. -/
def runAxioms (c y x : Nat) (s : ProofStore) : ProofStore :=
  let a := s.operand
  let b := s.cache + y
  ⟨if c = a ∨ c = b then 0 else bundle a b c,
    (heads a b c x).foldr pair (pair (all a s.cache) (pair s.top s.stack)), 0, 0⟩

theorem assign_same {V : Type} (s : Nat → V) (i : Nat) (v w : V) :
    assign (assign s i v) i w = assign s i w := by
  funext n
  by_cases h : n = i <;> simp [assign, h]

theorem assign_current {V : Type} (s : Nat → V) (i : Nat) :
    assign s i (s i) = s := by
  funext n
  by_cases h : n = i <;> simp [assign, h]

private theorem equal_witness {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (a b : Nat) (s : Nat → V) :
    Eval E s (ex a (equal a b)) := by
  rw [eval_ex s irrefl]
  refine ⟨s b, ?_⟩
  rw [eval_equal]
  by_cases same : b = a <;> simp [assign, same]

private theorem all_distribution {V : Type} {E : V → V → Prop} (a b c : Nat) (s : Nat → V) :
    Eval E s (imp (all a (imp b c)) (imp (all a b) (all a c))) := by
  simp only [eval_imp, eval_all]
  exact fun h j x => h x (j x)

private theorem all_commute {V : Type} {E : V → V → Prop} (a b c : Nat) (s : Nat → V) :
    Eval E s (imp (all a (all b c)) (all b (all a c))) := by
  simp only [eval_imp, eval_all]
  intro proof y x
  by_cases same : a = b
  · subst b
    exact proof y x
  · rw [assign_distinct s b a (Ne.symm same) y x]
    exact proof x y

private theorem all_self_instance {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (a b : Nat) (s : Nat → V) :
    Eval E s (imp (ex a (all a b)) b) := by
  simp only [eval_imp, eval_ex _ irrefl, eval_all]
  rintro ⟨x, hx⟩
  simpa only [assign_same, assign_current] using hx (s a)

private theorem propositional_head {V : Type} {E : V → V → Prop} (a b c x : Nat) (s : Nat → V) :
    Eval E s (imp (imp (imp c x) a) (imp (imp a c) (imp b c))) := by
  simp only [eval_imp]
  intro h ac _
  exact Classical.byContradiction fun nc => nc (ac (h (fun hc => (nc hc).elim)))

theorem heads_valid {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (a b c x formula : Nat) (member : formula ∈ heads a b c x) : Valid E formula := by
  simp only [heads, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact equal_witness irrefl a b
  · exact all_distribution a b c
  · intro s
    simp only [eval_imp, eval_equal, eval_mem]
    exact fun h mem => h ▸ mem
  · exact all_commute a b c
  · intro s
    simp only [eval_imp, eval_equal, eval_mem]
    exact fun h mem => h ▸ mem
  · exact all_self_instance irrefl a b
  · intro s
    simp only [eval_imp, eval_equal]
    exact fun ax bx => ax.symm.trans bx
  · exact propositional_head a b c x

def Subset {V : Type} (E : V → V → Prop) (a b : V) : Prop := ∀ z, E z a → E z b

/-- The semantic set principles needed for soundness of CXVG.
Collection is restricted to relations defined by numeric formulas. -/
structure BundleModel {V : Type} (E : V → V → Prop) : Prop where
  irrefl : ∀ x, ¬ E x x
  extensionality : ∀ a b, (∀ x, E x a ↔ E x b) → a = b
  empty : ∃ e, ∀ x, ¬ E x e
  container : ∀ a, ∃ d, E a d ∧ ∀ x, E x d →
    (∃ w, E w d ∧ ∀ y, Subset E y x → E y w) ∧ Subset E x d
  collect : ∀ (a b code : Nat) (s : Nat → V) (domain : V),
    let relation x y := Eval E (assign (assign s a x) b y) code
    ∃ image, (∀ x y, E x domain → relation x y → ∃ z, relation x z ∧ E z image) ∧
      (∀ y, E y image → ∃ x, relation x y)

theorem eval_subset {V : Type} {E : V → V → Prop} (s : Nat → V)
    {a b c : Nat} (left : a ≠ c) (right : b ≠ c) :
    Eval E s (subset c a b) ↔ Subset E (s a) (s b) := by
  simp only [subset, eval_all, eval_imp, eval_mem, Subset, assign, ite_eq_right left,
    ite_eq_right right, ite_true]

theorem extensionality_valid {V : Type} {E : V → V → Prop} (M : BundleModel E)
    {a b c : Nat} (left : a ≠ c) (right : b ≠ c) : Valid E (extensionalityCode a b c) := by
  intro s
  simp only [extensionalityCode, eval_imp, eval_equal, eval_subset s left right,
    eval_subset s right left]
  intro ab ba
  exact M.extensionality _ _ (fun z => ⟨ab z, ba z⟩)

theorem container_valid {V : Type} {E : V → V → Prop} (M : BundleModel E)
    {a b c : Nat} (left : a ≠ c) (right : b ≠ c) : Valid E (containerCode a b c) := by
  intro s
  obtain ⟨box, point, entries⟩ := M.container (s c)
  by_cases same : a = b
  · subst b
    simp only [containerCode, eval_ex _ M.irrefl, eval_and _ M.irrefl, eval_all, eval_imp,
      eval_mem, assign, ite_eq_right left.symm, ite_true]
    exact ⟨box, fun x hx => (M.irrefl x hx).elim, point⟩
  · simp only [containerCode, eval_ex _ M.irrefl, eval_and _ M.irrefl, eval_all, eval_imp,
      eval_mem, eval_subset _ left right, eval_subset _ right left, assign, ite_eq_right left,
      ite_eq_right right, ite_eq_right left.symm, ite_eq_right right.symm,
      ite_eq_right same, ite_eq_right (Ne.symm same), ite_true]
    refine ⟨box, fun x hx => ?_, point⟩
    obtain ⟨⟨bound, inBox, boundSpec⟩, included⟩ := entries x hx
    exact ⟨⟨bound, boundSpec, inBox⟩, included⟩

theorem collection_valid {V : Type} {E : V → V → Prop} (M : BundleModel E)
    {a b c : Nat} (left : a ≠ c) (right : b ≠ c) : Valid E (collectionCode a b c) := by
  intro s
  simp only [collectionCode, eval_ex _ M.irrefl, eval_and _ M.irrefl, eval_all, eval_imp, eval_mem]
  by_cases same : a = b
  · subst b
    obtain ⟨empty, noMembers⟩ := M.empty
    refine ⟨empty, fun x hx => ?_, fun y hy => ?_⟩
    · exact (M.irrefl x (by simpa [assign] using hx)).elim
    · exact (noMembers y (by simpa [assign, left.symm] using hy)).elim
  · obtain ⟨cover, covers, range⟩ := M.collect a b c s (s b)
    let env := assign s c cover
    have unchanged (x y : V) : Eval E (assign (assign env a x) b y) c ↔
        Eval E (assign (assign s a x) b y) c := by
      unfold env
      rw [assign_distinct s c a left.symm, assign_distinct (assign s a x) c b right.symm]
      exact eval_fresh E c c (Nat.le_refl _) _ cover
    refine ⟨cover, ?_, ?_⟩
    · intro x inDomain y related
      have declared : E x (s b) := by
        simpa [env, assign, Ne.symm same, right] using inDomain
      obtain ⟨z, relates, inCover⟩ := covers x y declared ((unchanged x y).1 related)
      refine ⟨z, ?_, ?_⟩
      · rw [assign_same]
        exact (unchanged x z).2 relates
      · simpa [env, assign, right.symm, left.symm] using inCover
    · intro y member
      have inCover : E y cover := by simpa [env, assign, right.symm] using member
      obtain ⟨x, relation⟩ := range y inCover
      refine ⟨x, ?_⟩
      rw [assign_distinct env b a (Ne.symm same)]
      exact (unchanged x y).2 relation

theorem bundle_valid {V : Type} {E : V → V → Prop} (M : BundleModel E)
    {a b c : Nat} (left : a ≠ c) (right : b ≠ c) : Valid E (bundle a b c) := by
  intro s
  simp only [bundle, eval_and _ M.irrefl]
  refine ⟨container_valid M left right s, extensionality_valid M left right s, ⟨?_, ?_⟩,
    collection_valid M left right s⟩
  · simp only [eval_imp, eval_all, eval_mem, assign, ite_eq_right left, ite_eq_right right]
    exact fun proof _ => proof
  · simp only [eval_imp, eval_all, eval_equal, assign, ite_eq_right left, ite_eq_right right]
    exact fun proof _ => proof

/-- Soundness of the numeric AX bundle, including its guard and saved
generalization. -/
theorem runAxioms_safe {V : Type} {E : V → V → Prop} (M : BundleModel E)
    (mode y formula : Nat) (s : ProofStore) (invariant : s.Invariant E) :
    (runAxioms mode y formula s).Invariant E := by
  have generalized : Valid E (all s.operand s.cache) := by
    intro env
    rw [eval_all]
    exact fun v => invariant.cache (assign env s.operand v)
  have saved := (validStack_pair s.top s.stack).2 ⟨invariant.top, invariant.stack⟩
  have base := (validStack_pair (all s.operand s.cache) _).2 ⟨generalized, saved⟩
  constructor
  · change Valid E (if mode = s.operand ∨ mode = s.cache + y then 0
      else bundle s.operand (s.cache + y) mode)
    split
    · exact valid_zero E
    · rename_i guards
      exact bundle_valid M (fun e => guards (Or.inl e.symm)) (fun e => guards (Or.inr e.symm))
  · exact CodeStack.foldr _ (fun _ member => heads_valid M.irrefl _ _ _ _ _ member) base
  · exact valid_zero E

end I0451.Logic
