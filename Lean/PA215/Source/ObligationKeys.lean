import PA215.Source.PathTrie
namespace PA215.Source.ObligationKeys

/-- Zero-branch/nonbranch use the even key; positive decrement uses the odd key. -/
def atSite (i : Nat) : Op → List Nat
  | .dec _ => [2*i,2*i+1]
  | _ => [2*i]

def required (start : Nat) : List Site → List Nat
  | [] => []
  | s::ss => atSite start s.op ++ required (start+1) ss

theorem required_append (xs ys : List Site) (start : Nat) :
    required start (xs++ys) = required start xs ++ required (start+xs.length) ys := by
  induction xs generalizing start with
  | nil => simp [required]
  | cons s xs ih =>
    simp only [List.cons_append,required,ih,List.length_cons,List.append_assoc]
    simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem required_prepend (b : Bool) (xs : List Site) (start : Nat) :
    required start (xs.map (PathTrie.prepend b)) = required start xs := by
  induction xs generalizing start with
  | nil => rfl
  | cons s xs ih => simp only [List.map_cons,required,PathTrie.prepend,ih]

def treeRequired (start : Nat) : PathTrie.Tree → List Nat
  | .leaf op => atSite start op
  | .node l r => treeRequired start l ++ treeRequired (start+PathTrie.size l) r

theorem treeRequired_eq (t : PathTrie.Tree) (start : Nat) :
    treeRequired start t = required start (PathTrie.flatten t) := by
  induction t generalizing start with
  | leaf op => simp [treeRequired,PathTrie.flatten,required]
  | node l r hl hr =>
    simp only [treeRequired,PathTrie.flatten,required_append,required_prepend,
      List.length_map,PathTrie.length_flatten,hl,hr]

theorem required_member (xs : List Site) (start i : Nat) (s : Site)
    (hs : xs[i]? = some s) (hk : k ∈ atSite (start+i) s.op) :
    k ∈ required start xs := by
  induction xs generalizing start i with
  | nil => simp at hs
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hs
      subst x
      exact List.mem_append_left _ (by simpa using hk)
    | succ i =>
      apply List.mem_append_right
      apply ih (start+1) i hs
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hk

#print axioms treeRequired_eq
#print axioms required_member
end PA215.Source.ObligationKeys
