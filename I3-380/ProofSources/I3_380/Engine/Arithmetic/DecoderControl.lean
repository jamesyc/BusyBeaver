module
public import I3_380.Engine.Arithmetic.RegisterWords
public import I3_380.Engine.DecoderWalk
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.Reference

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Engine (Decoded DecodedFrom Row)
open Engine.Port

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] referenceMachine Engine.transition

noncomputable def destination (d : Decoded) (l r : M) : M :=
  let e := d.transition
  if e.right then cell e.target (pushBit e.write (packWord d.before l)) r
  else fromLeft e.target (packWord d.before l) (pushBit e.write r)

/-- A bounded decoder walk reads only its consumed instruction bits.
The register blocks in the unexamined tail can have model-valued length. -/
theorem follow_reaches {fuel q : Nat} {previous input scanned : List Bool} {d : Decoded}
    (walk : DecodedFrom fuel q previous input scanned d) (active : q < 394)
    (height : 0 < Engine.height q) (validPrefix : Engine.PrefixValid q previous) (l r : M) :
    Reaches referenceMachine
      (cell q (packWord previous l) (packWord scanned r)) (destination d l r) := by
  have replay : ∀ (fuel q : Nat) (previous stem tail : List Bool) (d : Decoded),
      q < 394 → 0 < Engine.height q → Engine.PrefixValid q previous →
      Engine.follow fuel q previous (stem ++ tail) = some d →
      tail = d.rest →
      Reaches referenceMachine
        (cell q (packWord previous l) (packWord stem r)) (destination d l r) := by
    intro fuel
    induction fuel with
    | zero => simp [Engine.follow]
    | succ fuel ih =>
      intro q previous stem tail d hq hHeight hPrefix follows suffix
      cases stem with
      | nil =>
        subst tail
        have impossible : ∀ (n : Nat) (q : Nat) (p input : List Bool),
            Engine.follow n q p input = some d → d.rest.length < input.length := by
          intro n
          induction n with
          | zero => simp [Engine.follow]
          | succ n step =>
            intro q p input h
            cases input with
            | nil => simp [Engine.follow] at h
            | cons b rest =>
              simp only [Engine.follow] at h
              split at h
              · have shorter := step _ _ _ h
                simp only [List.length_cons]
                omega
              · cases exit : Engine.exitFor (Engine.transition q b).target with
                | none => simp [exit] at h
                | some command =>
                  simp only [exit,Option.map_some,Option.some.injEq] at h
                  rw [← h]
                  simp
        exact (Nat.lt_irrefl _ (impossible _ _ _ _ follows)).elim
      | cons b rest =>
        let edge := Engine.transition q b
        have row : Row q b edge.write edge.right edge.target := Engine.transition_row q b hq
        by_cases internal : 0 < Engine.height edge.target
        · obtain ⟨writes,moves,bound,_,nextPrefix⟩ :=
            Engine.internal_arm q b previous hq hHeight hPrefix internal
          have nextFollow : Engine.follow fuel edge.target (b :: previous) (rest ++ tail) = some d := by
            simpa only [List.cons_append,Engine.follow,show 0 < Engine.height (Engine.transition q b).target from internal,
              ↓reduceIte] using follows
          have move : Row q b b true edge.target := by rwa [writes,moves] at row
          change Reaches referenceMachine (cell q (packWord previous l)
            (pushBit b (packWord rest r))) (destination d l r)
          have remaining := ih edge.target (b :: previous) rest tail d bound internal nextPrefix nextFollow suffix
          exact (right move (packWord previous l) (packWord rest r)).trans remaining
        · simp only [List.cons_append,Engine.follow,show ¬0 < Engine.height (Engine.transition q b).target from internal,
            ↓reduceIte] at follows
          change (Engine.exitFor edge.target).map _ = some d at follows
          cases exit : Engine.exitFor edge.target with
          | none => simp [exit] at follows
          | some op =>
            simp only [exit,Option.map_some,Option.some.injEq] at follows
            subst d
            have empty : rest = [] := by
              change tail = rest ++ tail at suffix
              have h := congrArg List.length suffix
              simp at h
              simpa using h
            subst rest
            by_cases direction : edge.right = true
            · have move : Row q b edge.write true edge.target := direction ▸ row
              simpa only [destination,Decoded.transition,edge,direction,↓reduceIte,packWord,List.foldr_cons,List.foldr_nil]
                using right move (packWord previous l) r
            · have dir : edge.right = false := Bool.of_not_eq_true direction
              have move : Row q b edge.write false edge.target := dir ▸ row
              simpa only [destination,Decoded.transition,edge,dir,Bool.false_eq_true,↓reduceIte,packWord,List.foldr_cons,List.foldr_nil]
                using left move (packWord previous l) r
  exact replay fuel q previous scanned d.rest d active height validPrefix
    (by rw [walk.consumed]; exact walk.computed) rfl

structure RegisterRoute (path : List Bool) (dec : Bool) (r : Fin 12) : Prop where
  short : Engine.shortZeros 0 path.reverse = true
  run : ∀ tail : M, Reaches referenceMachine
    (cell root 1 (packWord path tail))
    (cell (registerEntry dec r.val) (packWord path.reverse 1) tail)

theorem register_route {input : List Bool} {d : Decoded}
    (walk : DecodedFrom 59 root [] input d.path d) {dec : Bool} {r : Fin 12}
    (command : d.command = .register dec r) : RegisterRoute (M := M) d.path dec r := by
  have shape := walk.shape
  rw [command] at shape
  obtain ⟨direction,write,short⟩ := shape
  have port := walk.port
  rw [command] at port
  change registerEntry dec r.val = d.transition.target at port
  have reversed : d.path.reverse = d.read :: d.before := by simp [Decoded.path]
  constructor
  · rwa [reversed]
  · intro tail
    have h := follow_reaches walk (by decide) (by rw [Engine.rootHeight]; decide) Engine.root_valid 1 tail
    simpa only [packWord,List.foldr_nil,List.foldr_cons,destination,Decoded.transition,direction,write,
      ↓reduceIte,port,reversed] using h

end PalomarI3380.ArithmeticMachine.Reference
