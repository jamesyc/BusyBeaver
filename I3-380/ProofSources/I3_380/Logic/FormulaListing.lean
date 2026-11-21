module
public import I3_380.Logic.Expanded
public import I3_380.Search.Cantor
@[expose] public section

namespace PalomarI3380.Logic.Expanded

structure Listing (V : Type) where
  get : Nat → V
  contains : ∀ x, ∃ i, get i = x

namespace Listing

variable {V : Type}

def argument (base : Listing V) (code : Nat) : Argument V :=
  let pair := Cantor.unpair code
  if pair.1 = 0 then .variable pair.2 else .named (base.get pair.2)

theorem argument_contains (base : Listing V) (arg : Argument V) : ∃ code, base.argument code = arg := by
  cases arg with
  | «variable» i => exact ⟨Cantor.pair 0 i, by simp [argument,Cantor.unpair_pair]⟩
  | named v =>
    obtain ⟨i, hi⟩ := base.contains v
    exact ⟨Cantor.pair 1 i, by simp [argument,Cantor.unpair_pair,hi]⟩

def decode (base : Listing V) : Nat → Nat → Formula V
  | 0, _ => .bot
  | fuel+1, code =>
    let tag := Cantor.unpair code
    let args := Cantor.unpair tag.2
    match tag.1 with
    | 0 => .eq (base.argument args.1) (base.argument args.2)
    | 1 => .mem (base.argument args.1) (base.argument args.2)
    | 2 => .order (base.argument args.1) (base.argument args.2)
    | 3 => .and (decode base fuel args.1) (decode base fuel args.2)
    | 4 => .or (decode base fuel args.1) (decode base fuel args.2)
    | 5 => .imp (decode base fuel args.1) (decode base fuel args.2)
    | 6 => .all (decode base fuel tag.2)
    | 7 => .ex (decode base fuel tag.2)
    | _ => .bot

theorem decode_covers (base : Listing V) (p : Formula V) :
    ∃ size code, ∀ fuel, size ≤ fuel → base.decode fuel code = p := by
  induction p with
  | bot =>
    refine ⟨1,Cantor.pair 8 0,?_⟩
    intro fuel h
    cases fuel <;> simp_all [decode,Cantor.unpair_pair]
  | eq a b | mem a b | order a b =>
    obtain ⟨i,ai⟩ := base.argument_contains a
    obtain ⟨j,bj⟩ := base.argument_contains b
    first
    | refine ⟨1,Cantor.pair 0 (Cantor.pair i j),?_⟩
      intro fuel h
      cases fuel <;> simp_all [decode,Cantor.unpair_pair]
      done
    | refine ⟨1,Cantor.pair 1 (Cantor.pair i j),?_⟩
      intro fuel h
      cases fuel <;> simp_all [decode,Cantor.unpair_pair]
      done
    | refine ⟨1,Cantor.pair 2 (Cantor.pair i j),?_⟩
      intro fuel h
      cases fuel <;> simp_all [decode,Cantor.unpair_pair]
      done
  | and a b ia ib | or a b ia ib | imp a b ia ib =>
    obtain ⟨s,i,ai⟩ := ia
    obtain ⟨t,j,bj⟩ := ib
    have first (fuel : Nat) (bound : max s t + 1 ≤ fuel + 1) : base.decode fuel i = a :=
      ai fuel (by omega)
    have second (fuel : Nat) (bound : max s t + 1 ≤ fuel + 1) : base.decode fuel j = b :=
      bj fuel (by omega)
    first
    | refine ⟨max s t + 1,Cantor.pair 3 (Cantor.pair i j),?_⟩
      intro fuel h
      cases fuel with
      | zero => omega
      | succ fuel => simp [decode,Cantor.unpair_pair,first fuel h,second fuel h]
      done
    | refine ⟨max s t + 1,Cantor.pair 4 (Cantor.pair i j),?_⟩
      intro fuel h
      cases fuel with
      | zero => omega
      | succ fuel => simp [decode,Cantor.unpair_pair,first fuel h,second fuel h]
      done
    | refine ⟨max s t + 1,Cantor.pair 5 (Cantor.pair i j),?_⟩
      intro fuel h
      cases fuel with
      | zero => omega
      | succ fuel => simp [decode,Cantor.unpair_pair,first fuel h,second fuel h]
      done
  | all a ih | ex a ih =>
    obtain ⟨s,i,body⟩ := ih
    have decoded (fuel : Nat) (bound : s + 1 ≤ fuel + 1) : base.decode fuel i = a :=
      body fuel (by omega)
    first
    | refine ⟨s+1,Cantor.pair 6 i,?_⟩
      intro fuel h
      cases fuel with
      | zero => omega
      | succ fuel => simp [decode,Cantor.unpair_pair,decoded fuel h]
      done
    | refine ⟨s+1,Cantor.pair 7 i,?_⟩
      intro fuel h
      cases fuel with
      | zero => omega
      | succ fuel => simp [decode,Cantor.unpair_pair,decoded fuel h]
      done

def formulas (base : Listing V) : Listing (Formula V) where
  get n := base.decode (Cantor.unpair n).1 (Cantor.unpair n).2
  contains p := by
    obtain ⟨fuel,code,done⟩ := base.decode_covers p
    exact ⟨Cantor.pair fuel code,by simpa [Cantor.unpair_pair] using done fuel (Nat.le_refl _)⟩

end Listing
end PalomarI3380.Logic.Expanded
