module
public import ModelReplay1914
public import ModelLiteralRecnStepCertificate
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1915 recnauxS2
theorem p1915 (e : Nat → M) (a0 : (M → Prop)) (a1 : M) (a2 : M) (predicate : ZF209.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0))) : (t10 (M := M) (t111 (M := M) (a2) (a0) (t29 (M := M) (a1))) (t63 (M := M) (t29 (M := M) (t64 (M := M) (t111 (M := M) (a2) (a0) (a1)))) (t84 (M := M) (a0) (t111 (M := M) (a2) (a0) (a1))))) := by
  let e1  : M := (t111 (M := M) (a2) (a0) ((show M from (t29 (M := M) (a1)))))
  let e2 (u0 : M) : M := (t64 (M := M) u0)
  let e3 (u0 : M) : M := (t29 (M := M) (e2 u0))
  let e4 (u0 : M) : M := (t84 (M := M) (a0) u0)
  let e5 (u0 : M) : M := (t63 (M := M) (e3 u0) (e4 u0))
  let e6  : (M → Prop) := (t82 (M := M) (fun x0_0 : M => (e5 x0_0)))
  let e8  : M := (t63 (M := M) ((show M from (t28 (M := M)))) (a2))
  let e10  : M := (t84 (M := M) (e6) ((show M from (t110 (M := M) (e8) (e6) (a1)))))
  let e11  : M := (t111 (M := M) (a2) (a0) (a1))
  let e12  : M := (t64 (M := M) (e11))
  let e13  : M := (t29 (M := M) (e12))
  let e14  : M := (t84 (M := M) (a0) (e11))
  let e15  : M := (t63 (M := M) (e13) (e14))
  let e16  : Prop := (t10 (M := M) (e1) (e10))
  let e17  : Prop := (t10 (M := M) (e10) (e15))
  let e20 (u0 : M) : Prop := (t10 (M := M) u0 (e11))
  have v0 := p342 (M := M) (e1) (e10) (e15)
  have v1 := p1905 (M := M) e (e8) (e6) (a1) (literalRecnStep_certificate predicate)
  have v2 : (e16) := (show (e16) from v1)
  have v3 := ((v0) (v2))
  have v4 := fun z0 : M => p1267 (M := M) z0 (e11)
  have v5 := fun z0 : M => p740 (M := M) (e20 z0) (e2 z0) (e12) (v4 z0)
  have v6 := fun z0 : M => p1480 (M := M) (a0) z0 (e11)
  have v7 := fun z0 : M => p1243 (M := M) (e20 z0) (e3 z0) (e13) (e4 z0) (e14) (v5 z0) (v6 z0)
  have v8 := p1494 (M := M) (e11) (e15) (fun w2 : M => (e5 w2)) ((fun w2 : M => v7 w2))
  have v9 : (e17) := (show (e17) from v8)
  have v10 := ((v3) (v9))
  exact v10

end ZF209.MM0ModelReplay
