module
public import ModelReplay2312
public import ModelFixedUpdateCertificate
public import ModelLiteralHistoryStepCertificate
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2313 srecauxS
theorem p2313 (e : Nat → M) (a0 : (M → Prop)) (a1 : M) (predicate : ZF209.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0))) : (t17 (M := M) (t120 (t137 (a0) (t29 (M := M) (a1)))) (t136 (t120 (t137 (a0) (a1))) (a1) (t84 (M := M) (a0) (t137 (a0) (a1))))) := by
  let e0  : M := (t137 (a0) (a1))
  let e1  : (M → Prop) := (t120 (e0))
  let e2  : M := (t84 (M := M) (a0) (e0))
  let e3  : (M → Prop) := (t136 (e1) (a1) (e2))
  let e5  : M := (t137 (a0) ((show M from (t29 (M := M) (a1)))))
  let e10  : M := (t121 (e3))
  let e13 (u0 : M) : (M → Prop) := (t120 u0)
  let e14 (u0 : M) : M := (t84 (M := M) (a0) u0)
  let e15 (u0 : M) (u1 : M) : (M → Prop) := (t136 (e13 u1) u0 (e14 u1))
  let e16 (u0 : M) (u1 : M) : M := (t121 (e15 u0 u1))
  let e17 (u0 : M) : (M → Prop) := (t82 (M := M) (fun x0_0 : M => (e16 u0 x0_0)))
  let e18  : (M → Prop) := (t89 (M := M) (fun x0_0 : M => (e17 x0_0)))
  let e19  : M := (t28 (M := M))
  let e22  : M := (t84 (M := M) (e18) ((show M from (t63 (M := M) (a1) ((show M from (t112 (M := M) (e19) (e18) (a1))))))))
  let e23  : Prop := (t10 (M := M) (e5) (e22))
  let e24  : Prop := (t10 (M := M) (e22) (e10))
  let e26 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e27 (u0 : M) : Prop := (t10 (M := M) u0 (e0))
  let e28 (u0 : M) (u1 : M) : Prop := (t2 (e26 u0) (e27 u1))
  let ee : Nat → M := fun i => Nat.casesOn i (e0) (fun i => Nat.casesOn i a1 (fun _ => e2))
  let updateCertificate : ZF209.MM0ModelPeano.FormulaCertificate ee 1 (fun v => e3 (v 0)) := fixedUpdate_certificate ee
  have v0 := p2098 (M := M) ee (e3) (e5) updateCertificate
  have v1 := p2301 (M := M) (e1) (a1) (e2)
  have v2 := p2090 (M := M) (e0)
  have v3 := ((v1) (v2))
  have v4 := ((v0) (v3))
  have v5 := p342 (M := M) (e5) (e22) (e10)
  have v6 := p1926 (M := M) e (e18) (a1) (e19) (literalHistoryStep_certificate predicate)
  have v7 : (e23) := (show (e23) from v6)
  have v8 := ((v5) (v7))
  have v9 := fun z0 : M => fun z1 : M => p54 (e26 z0) (e27 z1)
  have v10 := fun z0 : M => fun z1 : M => p2015 (M := M) (e28 z0 z1) z1 (e0) (v9 z0 z1)
  have v11 := fun z0 : M => fun z1 : M => p53 (e26 z0) (e27 z1)
  have v12 := fun z0 : M => fun z1 : M => p1479 (M := M) (e28 z0 z1) (a0) z1 (e0) (v9 z0 z1)
  have v13 := fun z0 : M => fun z1 : M => p2288 (M := M) (e28 z0 z1) (e13 z1) (e1) z0 (a1) (e14 z1) (e2) (v10 z0 z1) (v11 z0 z1) (v12 z0 z1)
  have v14 := fun z0 : M => fun z1 : M => p2091 (M := M) (e28 z0 z1) (e15 z0 z1) (e3) (v13 z0 z1)
  have v15 := fun z0 : M => p1495 (M := M) (e26 z0) (e0) (e10) (fun w3 : M => (e16 z0 w3)) ((fun w3 : M => v14 z0 w3))
  have v16 := p1539 (M := M) (a1) (e0) (e10) (fun w3 : M => (e17 w3)) ((fun w3 : M => v15 w3))
  have v17 : (e24) := (show (e24) from v16)
  have v18 := ((v8) (v17))
  have v19 := p118 ((show Prop from (t10 (M := M) (e5) (e10)))) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t120 (e5)))) (e3)))) (v4) (v18)
  exact v19

end ZF209.MM0ModelReplay
