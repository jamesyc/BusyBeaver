module
public import M209.SourceDefinitions
@[expose] public section
namespace M209.Source.TreeSource

inductive Primitive where
  | inc (logicalRegister : Nat)
  | dec (logicalRegister : Nat)
  | breakTo (depth : Nat)
  | continueTo (depth : Nat)
  | halt
  deriving DecidableEq, Repr

/-- Counts are redundant annotations. `wellFormed` checks every annotation,
so fast ordinal lookup cannot silently change the source-tree meaning. -/
inductive Tree where
  | leaf (op : Primitive)
  | node (leafCount : Nat) (left right : Tree)
  deriving Repr

def size : Tree → Nat
  | .leaf _ => 1
  | .node n _ _ => n

def primitiveValid : Primitive → Bool
  | .inc r | .dec r => r < 9
  | .breakTo n | .continueTo n => 0 < n
  | .halt => true

def wellFormed : Tree → Bool
  | .leaf op => primitiveValid op
  | .node n l r => n == size l + size r && wellFormed l && wellFormed r

def nthSite (t : Tree) (i : Nat) (pre : List Bool := []) : Option (List Bool × Primitive) :=
  match t with
  | .leaf op => if i = 0 then some (pre,op) else none
  | .node _ l r =>
    if i < size l then nthSite l i (pre ++ [false])
    else nthSite r (i-size l) (pre ++ [true])

/-- Prefix lookup returns the first leaf under that source prefix. At a leaf,
remaining zero padding denotes that same leftmost leaf, as in the source machine. -/
def locate (t : Tree) (path : List Bool) (base : Nat := 0) : Option Nat :=
  match path,t with
  | [], _ => some base
  | _, .leaf _ => if path.all (! ·) then some base else none
  | false :: p, .node _ l _ => locate l p base
  | true :: p, .node _ l r => locate r p (base+size l)

def successorRev : List Bool → Option (List Bool)
  | [] => none
  | false :: p => some (true :: p)
  | true :: p => (successorRev p).map (false :: ·)

def successor (path : List Bool) : Option (List Bool) :=
  (successorRev path.reverse).map List.reverse

def cutRev (edge : Bool) : Nat → List Bool → Option (List Bool)
  | 0,p => some p
  | _+1,[] => none
  | n+1,b::p => if b = edge then cutRev edge n p else cutRev edge (n+1) p

def cut (path : List Bool) (edge : Bool) (depth : Nat) : Option (List Bool) :=
  (cutRev edge depth path.reverse).map List.reverse

def after (t : Tree) (path : List Bool) : Option Nat :=
  (successor path).bind (locate t ·)

def physicalRegister (r : Nat) : Nat :=
  match r with
  | 0 => 6 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 3
  | 5 => 7 | 6 => 8 | 7 => 5 | _ => 1

def resolveSite (tree : Tree) (site : List Bool × Primitive) : Option Instruction :=
  let (path,op) := site
  match op with
  | .inc r => (after tree path).map (.inc (physicalRegister r))
  | .dec r => do
    let scope ← cut path false 1
    let zero ← after tree scope
    let positive ← after tree path
    return .dec (physicalRegister r) zero positive
  | .breakTo depth => do
    let scope ← cut path false depth
    let target ← after tree scope
    return .jump target
  | .continueTo depth => do
    let scope ← cut path true depth
    let target ← locate tree scope
    return .jump target
  | .halt => some .halt

def resolve (tree : Tree) (i : Nat) : Option Instruction :=
  (nthSite tree i).bind (resolveSite tree)

def treePath (tree : Tree) (i : Nat) : List Bool :=
  ((nthSite tree i).map Prod.fst).getD []
end M209.Source.TreeSource
