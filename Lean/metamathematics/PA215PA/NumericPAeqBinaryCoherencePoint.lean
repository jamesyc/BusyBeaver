module

public import PA215PA.NumericPAeqBinaryCoherenceRelation

@[expose] public section
namespace PA215.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : InternalTheory V RelationalSource.language}
noncomputable def binaryCoherenceAt {Γ:ND.Seq (V:=V)} (D P Q U W:SF (V:=V) 1)
    (F:SF (V:=V) 3) (R:SF (V:=V) 2) (x y b c r s:ST (V:=V) 0)
    (h:ND.Proof (T:=T) Γ (binaryRelation D F R))
    (hi:ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R))
    (hj:ND.Proof (T:=T) Γ (pairwise (D ⋏ Q) (D ⋏ W) R))
    (hp:ND.Proof (T:=T) Γ (unary (D ⋏ P) x)) (hu:ND.Proof (T:=T) Γ (unary (D ⋏ U) y))
    (hq:ND.Proof (T:=T) Γ (unary (D ⋏ Q) b)) (hw:ND.Proof (T:=T) Γ (unary (D ⋏ W) c))
    (hr:ND.Proof (T:=T) Γ (ternary F x b r)) (hs:ND.Proof (T:=T) Γ (ternary F y c s)) :
    ND.Proof (T:=T) Γ (binary R r s) := by
  have dx : ND.Proof (T:=T) Γ (unary D x) := ND.andLeft (q := unary P x) (by simpa [unary] using hp)
  have dy : ND.Proof (T:=T) Γ (unary D y) := ND.andLeft (q := unary U y) (by simpa [unary] using hu)
  have db : ND.Proof (T:=T) Γ (unary D b) := ND.andLeft (q := unary Q b) (by simpa [unary] using hq)
  have dc : ND.Proof (T:=T) Γ (unary D c) := ND.andLeft (q := unary W c) (by simpa [unary] using hw)
  exact binaryRelationAt D F R x y b c r s h dx dy db dc
    (pairwiseAt (D ⋏ P) (D ⋏ U) R x y hi hp hu)
    (pairwiseAt (D ⋏ Q) (D ⋏ W) R b c hj hq hw) hr hs
#print axioms binaryCoherenceAt
end PA215.PA.NumericPAeqValueCoherence
