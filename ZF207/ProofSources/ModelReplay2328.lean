module
public import ModelReplay2326
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2327 sreclem2
theorem p2327 (e : Nat → M) (a0 : M) (a1 : M) (a3 : M → M) (a4 : M → M) (graph : ZF207.MM0ModelPeano.FunctionGraphCertificate e 1 (fun v => a3 (v 0)))  : (∀ z0 : M, (t0 (t10 (M := M) (a0) (t135 (M := M) (t124 (a1)) (fun x2_0 : M => (a3 x2_0)))) (t0 (t48 (M := M) (a4 z0) (a1)) (t10 (M := M) (t84 (M := M) (t120 (a0)) (a4 z0)) (t43 (M := M) (a4 z0) (fun x3_1 : M => (a3 x3_1))))))) := by
  let e0  : (M → Prop) := (t82 (M := M) (fun x0_0 : M => (a3 x0_0)))
  let e1  : M := (t124 (a1))
  let e2  : (M → Prop) := (t120 (e1))
  let e3  : (M → Prop) := (t81 (M := M) (e0) (e2))
  let e6  : (M → Prop) := (t120 (a0))
  let e9  : Prop := (t10 (M := M) (a0) ((show M from (t121 (e3)))))
  let e12  : Prop := (t10 (M := M) (a0) ((show M from (t135 (M := M) (e1) (fun x0_0 : M => (a3 x0_0))))))
  let e13 (u0 : M) : Prop := (t48 (M := M) (a4 u0) (a1))
  let e14 (u0 : M) : Prop := (t2 (e12) (e13 u0))
  let e15 (u0 : M) : Prop := (t0 (e14 u0) (e9))
  let e16 (u0 : M) : Prop := (t16 (M := M) (a4 u0) (e2))
  let e17 (u0 : M) : M := (t84 (M := M) (e3) (a4 u0))
  let e18 (u0 : M) : M := (t84 (M := M) (e0) (a4 u0))
  let e19 (u0 : M) : Prop := (t10 (M := M) (e17 u0) (e18 u0))
  let e20 (u0 : M) : M := (t84 (M := M) (e6) (a4 u0))
  let e21 (u0 : M) : M := (t43 (M := M) (a4 u0) (fun x0_1 : M => (a3 x0_1)))
  let e22 (u0 : M) : Prop := (t10 (M := M) (e20 u0) (e21 u0))
  let ee : Nat → M := fun i => Nat.casesOn i e1 e
  let restrictionCertificate : ZF207.MM0ModelPeano.FormulaCertificate ee 1 (fun v => e3 (v 0)) :=
    literalRestrictedGraph_certificate (literalBitAt_certificate ee 0) (graph.prependParameter e1)
  have v0 := fun z0 : M => p1492 (M := M) (fun w0 : M => (a3 w0)) (fun w0 : M => (a4 w0)) z0
  have v1 := p2098 (M := M) ee (e3) (a0) restrictionCertificate
  have v2 := p1449 (M := M) e (e2) (fun w1 : M => (a3 w1)) graph
  have v3 := p2090 (M := M) (e1)
  have v4 := ((v2) (v3))
  have v5 := ((v1) (v4))
  have v6 := fun z0 : M => p53 (e12) (e13 z0)
  have v7 : (∀ z0 : M, (e15 z0)) := (show (∀ z0 : M, (e15 z0)) from v6)
  have v8 := fun z0 : M => p154 (e14 z0) (e9) ((show Prop from (t17 (M := M) (e6) (e3)))) (v5) (v7 z0)
  have v9 := fun z0 : M => p1477 (M := M) (e14 z0) (e6) (e3) (a4 z0) (v8 z0)
  have v10 := fun z0 : M => p1490 (M := M) (e2) (e0) (a4 z0)
  have v11 := fun z0 : M => p2139 (M := M) (a4 z0) (a1)
  have v12 := fun z0 : M => p54 (e12) (e13 z0)
  have v13 := fun z0 : M => p154 (e14 z0) (e13 z0) (e16 z0) (v11 z0) (v12 z0)
  have v14 := fun z0 : M => p10 (e14 z0) (e16 z0) (e19 z0) (v10 z0) (v13 z0)
  have v15 := fun z0 : M => p357 (M := M) (e14 z0) (e20 z0) (e17 z0) (e18 z0) (v9 z0) (v14 z0)
  have v16 := fun z0 : M => p362 (M := M) (e14 z0) (e20 z0) (e18 z0) (e21 z0) (v0 z0) (v15 z0)
  have v17 := fun z0 : M => p84 (e12) (e13 z0) (e22 z0) (v16 z0)
  exact v17
-- Actual MMB 2328 srecval
theorem p2328 (e : Nat → M) (a1 : (M → Prop)) (a2 : M) (predicate : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a1 (v 0)))  : (t10 (M := M) (t138 (a1) (a2)) (t84 (M := M) (a1) (t135 (M := M) (t124 (a2)) (fun x2_0 : M => (t138 (a1) x2_0))))) := by
  let e1  : M := (t137 (a1) (a2))
  let e3  : M := (t124 (a2))
  let e4 (u0 : M) : M := (t138 (a1) u0)
  let e5  : M := (t135 (M := M) (e3) (fun x0_0 : M => (e4 x0_0)))
  let e11  : (M → Prop) := (t120 (e1))
  let e12  : M := (t121 (e11))
  let e15  : (M → Prop) := (t81 (M := M) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (e4 x0_0))))) ((show (M → Prop) from (t120 (e3)))))
  let e18  : Prop := (t0 ((show Prop from (t17 (M := M) (e15) (e11)))) ((show Prop from (t10 (M := M) (e5) (e12)))))
  have v0 := p344 (M := M) ((show M from (t138 (a1) (a2)))) ((show M from (t84 (M := M) (a1) (e1)))) ((show M from (t84 (M := M) (a1) (e5))))
  have v1 := p2323 (M := M) e (a1) (a2) predicate
  have v2 := ((v0) (v1))
  have v3 := p1480 (M := M) (a1) (e5) (e1)
  have v4 := p342 (M := M) (e5) (e12) (e1)
  have v5 := p2092 (M := M) (e15) (e11)
  have v6 : (e18) := (show (e18) from v5)
  have v7 := p2324 (M := M) e (a1) (a2) predicate
  have v8 := ((v6) (v7))
  have v9 := ((v4) (v8))
  have v10 := p2096 (M := M) (e1)
  have v11 := ((v9) (v10))
  have v12 := ((v3) (v11))
  have v13 := ((v2) (v12))
  exact v13

end ZF207.MM0ModelReplay
