module
public import NumericTheory
@[expose] public section
namespace ZFR.ExecutableZF

def boundCheck : Formula → Nat → Bool
 | .bot, _ => true
 | .mem i j, n | .eq i j, n => decide (i < n) && decide (j < n)
 | .and p q, n | .or p q, n | .imp p q, n => boundCheck p n && boundCheck q n
 | .all p, n | .ex p, n => boundCheck p (n + 1)

theorem boundCheck_iff (p : Formula) (n : Nat) : boundCheck p n = true ↔ Bound p n := by
 induction p generalizing n <;> simp_all [boundCheck, Bound]

/-- Explicit finite schema witness, rather than an unbounded existential search.
These can be enumerated alongside proof certificates. Choice is absent. -/
inductive AxiomWitness where
 | refl | sym | trans | eqElem | ext | empty | pair | union | power | omega | foundation
 | separation (parameters : Nat) (body : Formula)
 | replacement (parameters : Nat) (body : Formula)
 deriving Repr

abbrev CheckedAxiom := { a : Formula // sourceZfrAxiom (encodeFormula a) }

def checkAxiom : AxiomWitness → Option CheckedAxiom
 | .refl => some ⟨fixedRefl, by simp [sourceZfrAxiom, sourceZfrFixed]⟩
 | .sym => some ⟨fixedSym, by simp [sourceZfrAxiom, sourceZfrFixed]⟩
 | .trans => some ⟨fixedTrans, by simp [sourceZfrAxiom, sourceZfrFixed]⟩
 | .eqElem => some ⟨fixedEqElem, by simp [sourceZfrAxiom, sourceZfrFixed]⟩
 | .ext => some ⟨fixedExt, by simp [sourceZfrAxiom, sourceZfrFixed]⟩
 | .empty => some ⟨fixedEmpty, by simp [sourceZfrAxiom, sourceZfrFixed]⟩
 | .pair => some ⟨fixedPair, by simp [sourceZfrAxiom, sourceZfrFixed]⟩
 | .union => some ⟨fixedUnion, by simp [sourceZfrAxiom, sourceZfrFixed]⟩
 | .power => some ⟨fixedPower, by simp [sourceZfrAxiom, sourceZfrFixed]⟩
 | .omega => some ⟨fixedOmega, by simp [sourceZfrAxiom, sourceZfrFixed]⟩
 | .foundation => some ⟨fixedFoundation, by simp [sourceZfrAxiom, sourceZfrFixed]⟩
 | .separation n p =>
   if h : boundCheck p (n + 1) = true then
     some ⟨separationSchema n p, separationSchema_in_zfr n p ((boundCheck_iff p _).mp h)⟩
   else none
 | .replacement n p =>
   if h : boundCheck p (n + 2) = true then
     some ⟨replacementSchema n p, replacementSchema_in_zfr n p ((boundCheck_iff p _).mp h)⟩
   else none

def axiomFormula (w : AxiomWitness) : Option Formula := (checkAxiom w).map Subtype.val

theorem sound (w : AxiomWitness) (a : Formula) (ha : axiomFormula w = some a) :
    sourceZfrAxiom (encodeFormula a) := by
 unfold axiomFormula at ha
 cases h : checkAxiom w with
 | none => simp [h] at ha
 | some result =>
   have eq : result.val = a := by simpa [h] using ha
   exact eq ▸ result.property

end ZFR.ExecutableZF
