module
public import ModelReplay2322
public import ModelLiteralCourseRecCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2323 srecval2
theorem p2323 (e : Nat → M) (a0 : (M → Prop)) (a1 : M) (predicate : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0)))  : (t10 (M := M) (t138 (a0) (a1)) (t84 (M := M) (a0) (t137 (a0) (a1)))) := by
  let e1  : M := (t29 (M := M) (a1))
  let e3  : (M → Prop) := (t120 ((show M from (t137 (a0) (e1)))))
  let e4  : M := (t84 (M := M) (e3) (a1))
  let e5  : M := (t137 (a0) (a1))
  let e6  : M := (t84 (M := M) (a0) (e5))
  let e12  : (M → Prop) := (t120 (e5))
  let e13  : (M → Prop) := (t136 (e12) (a1) (e6))
  have v0 := p332 (M := M) ((show M from (t138 (a0) (a1)))) (e4) (e6)
  have v1 := p2322 (M := M) e (a0) (a1) (e1) predicate
  have v2 := p902 (M := M) (a1)
  have v3 := ((v1) (v2))
  have v4 := ((v0) (v3))
  have v5 := p342 (M := M) (e4) ((show M from (t84 (M := M) (e13) (a1)))) (e6)
  have v6 := p1478 (M := M) (e3) (e13) (a1)
  have v7 := p2313 (M := M) e (a0) (a1) predicate
  have v8 := ((v6) (v7))
  have v9 := ((v5) (v8))
  have v10 := p2297 (M := M) (e12) (a1) (e6)
  have v11 := ((v9) (v10))
  have v12 := ((v4) (v11))
  exact v12
-- Actual MMB 2324 srecres
theorem p2324 (e : Nat → M) (a0 : (M → Prop)) (a2 : M) (predicate : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0)))  : (t17 (M := M) (t81 (M := M) (t82 (M := M) (fun x2_0 : M => (t138 (a0) x2_0))) (t120 (t124 (a2)))) (t120 (t137 (a0) (a2)))) := by
  let e0 (u0 : M) : M := (t138 (a0) u0)
  let e3  : (M → Prop) := (t120 ((show M from (t124 (a2)))))
  let e6  : (M → Prop) := (t120 ((show M from (t137 (a0) (a2)))))
  let e7 (u0 : M) : M := (t84 (M := M) (e6) u0)
  let e8  : (M → Prop) := (t82 (M := M) (fun x0_0 : M => (e7 x0_0)))
  let e9  : (M → Prop) := (t81 (M := M) (e8) (e3))
  let e10 (u0 : M) : Prop := (t16 (M := M) u0 (e3))
  let e11 (u0 : M) : Prop := (t48 (M := M) u0 (a2))
  let e12 (u0 : M) : Prop := (t10 (M := M) (e7 u0) (e0 u0))
  let e13 (u0 : M) : Prop := (t0 (e10 u0) (e12 u0))
  let e19  : (M → Prop) := (t76 (M := M) (e6))
  let e20  : (M → Prop) := (t81 (M := M) (e8) (e19))
  have v0 := p559 (M := M) ((show (M → Prop) from (t81 (M := M) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (e0 x0_0))))) (e3)))) (e9) (e6)
  have v1 := p1455 (M := M) (e3) (fun w1 : M => (e7 w1)) (fun w1 : M => (e0 w1))
  have v2 := fun z0 : M => p2139 (M := M) z0 (a2)
  have v3 := fun z0 : M => p2322 (M := M) e (a0) z0 (a2) predicate
  have v4 := fun z0 : M => p155 (e10 z0) (e11 z0) (e12 z0) (v2 z0) (v3 z0)
  have v5 := b325 (M := M) (fun w0 : M => (e13 w0)) ((fun w0 : M => v4 w0))
  have v6 := ((v1) (v5))
  have v7 := ((v0) (v6))
  have v8 := p559 (M := M) (e9) (e20) (e6)
  have v9 := p1421 (M := M) (e8) (e19) (e3)
  have v10 := p2314 (M := M) e (a0) (a2) predicate
  have v11 := ((v9) (v10))
  have v12 := ((v8) (v11))
  have v13 := p1499 (M := M) (e6)
  have v14 := p2315 (M := M) e (a0) (a2) predicate
  have v15 := p118 ((show Prop from (t72 (M := M) (e6)))) ((show Prop from (t17 (M := M) (e20) (e6)))) (v13) (v14)
  have v16 := ((v12) (v15))
  have v17 := ((v7) (v16))
  exact v17
-- Actual MMB 2325 srecrlam
theorem p2326 (e : Nat → M) (a0 : M) (a1 : M) (a3 : M → M) (graph : ZF207.MM0ModelPeano.FunctionGraphCertificate e 1 (fun v => a3 (v 0)))  : (t0 (t10 (M := M) (a0) (t135 (M := M) (t124 (a1)) (fun x2_0 : M => (a3 x2_0)))) (t10 (M := M) (t125 (t76 (M := M) (t120 (a0)))) (a1))) := by
  let e0  : M := (t124 (a1))
  let e1  : M := (t135 (M := M) (e0) (fun x0_0 : M => (a3 x0_0)))
  let e2  : Prop := (t10 (M := M) (a0) (e1))
  let e3  : (M → Prop) := (t120 (a0))
  let e4  : (M → Prop) := (t120 (e1))
  let e5  : (M → Prop) := (t76 (M := M) (e3))
  let e7  : (M → Prop) := (t120 (e0))
  have v0 := p2150 (M := M) (a1)
  have v1 := p2267 (M := M) e (fun w0 : M => (e0)) (fun w0 : M => (a3 w0)) graph 0
  have v2 := p2016 (M := M) (a0) (e1)
  have v3 := p1376 (M := M) (e2) (e3) (e4) (v2)
  have v4 := p568 (M := M) (e5) ((show (M → Prop) from (t76 (M := M) (e4)))) (e7) (e2) (v1) (v3)
  have v5 := p2145 (M := M) (e2) (e5) (e7) (v4)
  have v6 := p362 (M := M) (e2) ((show M from (t125 (e5)))) ((show M from (t125 (e7)))) (a1) (v0) (v5)
  exact v6

end ZF207.MM0ModelReplay
