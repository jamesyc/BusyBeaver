module
public import I3_380.WordCode
public import I3_380.Ground
@[expose] public section

namespace PalomarI3380

/-- The actual word verifier admits every tag at every arity. Arity
is the number of children stored in the application. -/
inductive RawTerm where
  | app (tag : Nat) (children : List RawTerm)

namespace RawTerm

def fold {A : Type} (op : Nat → List A → A) : RawTerm → A
  | .app tag children => op tag (children.attach.map fun child => fold op child.val)
termination_by tree => sizeOf tree
decreasing_by
  have h := List.sizeOf_lt_of_mem child.property
  simp_wf
  omega

@[simp] theorem fold_app {A : Type} (op : Nat → List A → A) (tag : Nat) (children : List RawTerm) :
    fold op (.app tag children) = op tag (children.map (fold op)) := by
  unfold fold
  rw [List.attach_map_val]

def tokens (term : RawTerm) : List Token :=
  term.fold fun tag children => ⟨children.length, tag⟩ :: children.flatten

@[simp] theorem tokens_app (tag : Nat) (children : List RawTerm) :
    (RawTerm.app tag children).tokens = ⟨children.length, tag⟩ :: children.flatMap RawTerm.tokens := by
  simp only [fold_app, List.length_map, List.flatMap_def, tokens]
  rfl

/-- Unknown tags are interpreted as the constant top operation. This
extension leaves every original operation and axiom intact. -/
def operation {A : Type} (M : Algebra A) (tag : Nat) (args : List A) : A :=
  match args with
  | [] =>
    match tag with
    | 0 => M.constant .J
    | 1 => M.constant .D
    | 2 => M.constant .T
    | 3 => M.constant .S
    | 5 => M.constant .E
    | 6 => M.constant .I
    | _ => M.constant .U
  | [x] =>
    match tag with
    | 0 => M.neg x
    | 1 => M.choice x
    | 2 => M.localRel x
    | 3 => M.converse x
    | _ => M.constant .U
  | [x, y] =>
    match tag with
    | 0 => M.nand x y
    | 1 => M.product x y
    | _ => M.constant .U
  | [x, y, z] =>
    if tag = 0 then M.node x y z else M.constant .U
  | _ => M.constant .U

def evaluate {A : Type} (M : Algebra A) (t : RawTerm) : A := t.fold (operation M)

@[simp] theorem evaluate_app {A : Type} (M : Algebra A) (tag : Nat) (children : List RawTerm) :
    (RawTerm.app tag children).evaluate M = operation M tag (children.map (evaluate M)) :=
  fold_app _ _ _

end RawTerm

def Term.toRaw {V : Type} (substitution : V → RawTerm) : Term V → RawTerm
  | .var v => substitution v
  | .const c => .app c.tag []
  | .neg x => .app 0 [x.toRaw substitution]
  | .choice x => .app 1 [x.toRaw substitution]
  | .localRel x => .app 2 [x.toRaw substitution]
  | .converse x => .app 3 [x.toRaw substitution]
  | .nand x y => .app 0 [x.toRaw substitution, y.toRaw substitution]
  | .product x y => .app 1 [x.toRaw substitution, y.toRaw substitution]
  | .node x y z => .app 0 [x.toRaw substitution, y.toRaw substitution, z.toRaw substitution]

theorem Term.evaluate_toRaw {A V : Type} (M : Algebra A) (substitution : V → RawTerm) (t : Term V) :
    (t.toRaw substitution).evaluate M = M.eval (fun v => (substitution v).evaluate M) t := by
  induction t <;> simp only [Term.toRaw, RawTerm.evaluate_app, List.map_cons, List.map_nil,
    Algebra.eval, RawTerm.operation, ↓reduceIte, *]
  case const c => cases c <;> rfl

private theorem fuse_emitted {V : Type} (t : Term V) (v : V → List Token)
    (base tail : List Token) : t.emit v base ++ tail = t.emit v (base ++ tail) :=
  (t.emit_append v base tail).symm

theorem Term.tokens_toRaw_append {V : Type} (substitution : V → RawTerm) (t : Term V)
    (tail : List Token) :
    (t.toRaw substitution).tokens ++ tail = t.emit (fun v => (substitution v).tokens) tail := by
  induction t generalizing tail <;> simp only [Term.toRaw, RawTerm.tokens_app, List.length_nil,
    List.length_cons, List.flatMap_cons, List.flatMap_nil, List.nil_append,
    List.cons_append, Term.emit, Nat.zero_add, fuse_emitted, *]

theorem Term.tokens_toRaw {V : Type} (substitution : V → RawTerm) (t : Term V) :
    (t.toRaw substitution).tokens = t.emit (fun v => (substitution v).tokens) [] := by
  simpa only [List.append_nil] using t.tokens_toRaw_append substitution []

/-- A hole in a ground term. The two child lists record its siblings. -/
inductive RawContext where
  | hole
  | app (tag : Nat) (before : List RawTerm) (nested : RawContext) (after : List RawTerm)

def RawContext.fill (ctx : RawContext) (t : RawTerm) : RawTerm :=
  match ctx with
  | .hole => t
  | .app tag before nested after => .app tag (before ++ nested.fill t :: after)

theorem RawContext.evaluate_eq {A : Type} (ctx : RawContext) (M : Algebra A)
    {s t : RawTerm} (h : s.evaluate M = t.evaluate M) :
    (ctx.fill s).evaluate M = (ctx.fill t).evaluate M := by
  induction ctx with
  | hole => exact h
  | app tag before nested after ih =>
    simp only [RawContext.fill, RawTerm.evaluate_app, List.map_append, List.map_cons, ih]

end PalomarI3380
