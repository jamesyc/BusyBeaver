module
public import I3_334Support.Logic.ExpandedTemplates
public import I3_334Support.Logic.NamedParameters
@[expose] public section

namespace PalomarI3380.Logic.Expanded

variable {X Y : Type}

def Argument.mapNames (f : X → Y) : Argument X → Argument Y
  | .variable i => .variable i
  | .named x => .named (f x)

def Formula.mapNames (f : X → Y) : Formula X → Formula Y
  | .bot => .bot
  | .eq a b => .eq (a.mapNames f) (b.mapNames f)
  | .mem a b => .mem (a.mapNames f) (b.mapNames f)
  | .order a b => .order (a.mapNames f) (b.mapNames f)
  | .and p q => .and (p.mapNames f) (q.mapNames f)
  | .or p q => .or (p.mapNames f) (q.mapNames f)
  | .imp p q => .imp (p.mapNames f) (q.mapNames f)
  | .all p => .all (p.mapNames f)
  | .ex p => .ex (p.mapNames f)

theorem Argument.mapNames_rename (a : Argument X) (f : X → Y) (σ : Nat → Nat) :
    (a.rename σ).mapNames f = (a.mapNames f).rename σ := by cases a <;> rfl

theorem Argument.mapNames_bound (a : Argument X) (f : X → Y) (n : Nat) :
    (a.mapNames f).bound n ↔ a.bound n := by cases a <;> rfl

theorem mapNames_bound (p : Formula X) (f : X → Y) (n : Nat) :
    Bound (p.mapNames f) n ↔ Bound p n := by
  induction p generalizing n <;> simp only [Formula.mapNames, Bound,Argument.mapNames_bound, *]

theorem Argument.mapNames_names (a : Argument X) (f : X → Y) :
    (a.mapNames f).names = a.names.map f := by cases a <;> rfl

theorem mapNames_names (p : Formula X) (f : X → Y) :
    (p.mapNames f).names = p.names.map f := by
  induction p <;> simp only [Formula.names,Formula.mapNames,Argument.mapNames_names,List.map_append,List.map_nil , *]

theorem Argument.mapNames_lower (a : Argument X) (f : X → Y) (slot : Y → Nat) (n : Nat) :
    (a.mapNames f).lower slot n = a.lower (slot ∘ f) n := by cases a <;> rfl

theorem mapNames_lower (p : Formula X) (f : X → Y) (slot : Y → Nat) (n : Nat) :
    (p.mapNames f).lower slot n = p.lower (slot ∘ f) n := by
  induction p generalizing n <;> simp only [Formula.mapNames,Formula.lower,Argument.mapNames_lower , *]

theorem Argument.mapNames_substitute (a : Argument X) (f : X → Y) (args : Nat → Argument X) :
    (a.substitute args).mapNames f = (a.mapNames f).substitute (fun i => (args i).mapNames f) := by
  cases a <;> rfl

theorem mapNames_substitute (p : Formula X) (f : X → Y) (args : Nat → Argument X) :
    (p.substitute args).mapNames f = (p.mapNames f).substitute (fun i => (args i).mapNames f) := by
  have liftMap (args : Nat → Argument X) :
      (fun i => (liftNames args i).mapNames f) =
        liftNames (fun i => (args i).mapNames f) := by
    funext i
    cases i with
    | zero => rfl
    | succ i => exact Argument.mapNames_rename _ _ _
  induction p generalizing args <;>
    simp only [Formula.mapNames,Formula.substitute,Argument.mapNames_substitute,liftMap , *]

theorem mapNames_membership (p : Logic.Formula) (f : X → Y) :
    (Formula.membership p).mapNames f = Formula.membership p := by
  induction p <;> simp only [Formula.membership,Formula.mapNames,Argument.mapNames , *]

theorem mapNames_template (p : SetFormula) (n : Nat) (args : Nat → Argument X) (f : X → Y) :
    (applyTemplate p n args).mapNames f = applyTemplate p n (fun i => (args i).mapNames f) := by
  simp only [applyTemplate,mapNames_substitute,mapNames_membership]

end PalomarI3380.Logic.Expanded
