module
public import ExactBinderDescent
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma model_natCast_strictMono : StrictMono (fun n : Nat => (n:M)) := by
 apply strictMono_nat_of_lt_succ
 intro n
 change (n:M)<(n:M)+1
 exact lt_add_one (n:M)

lemma model_natCast_lt {m n : Nat} (h : m<n) : (m:M)<(n:M) :=
 model_natCast_strictMono h

end ZFR.ArithmeticRepresentation
