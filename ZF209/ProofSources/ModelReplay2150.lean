module
public import ModelReplay2146
public import ModelBoundPredicateCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2147 sssize
theorem p2147 (e : Nat → M) (a0 : (M → Prop)) (predicate : ZF209.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0)))  : (t3 (t49 (M := M) (a0)) (t18 (M := M) (a0) (t120 (t124 (t125 (a0)))))) := by
  let e1 (u0 : M) : M := (t124 u0)
  let e2 (u0 : M) : (M → Prop) := (t120 (e1 u0))
  let e3 (u0 : M) : Prop := (t18 (M := M) (a0) (e2 u0))
  let e4  : Prop := (t9 (M := M) (fun x0_0 : M => (e3 x0_0)))
  let e5  : M := (t125 (a0))
  let e6  : M := (t124 (e5))
  let e7  : (M → Prop) := (t120 (e6))
  let e8  : Prop := (t18 (M := M) (a0) (e7))
  let e13 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e14 (u0 : M) : M := (t124 u0)
  let e15 (u0 : M) : (M → Prop) := (t120 (e14 u0))
  let e16 (u0 : M) : Prop := (t18 (M := M) (a0) (e15 u0))
  let e17 (u0 : M) : Prop := (t10 (M := M) u0 (e5))
  let e18  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e16 x0_0)))
  let e19 (u0 : M) : Prop := (t16 (M := M) u0 (e18))
  let e20  : Prop := (t16 (M := M) (e5) (e18))
  let e21 (u0 : M) : Prop := (t0 (e19 u0) (e20))
  let e22 (u0 : M) : Prop := (t10 (M := M) u0 (e5))
  have v0 := p149 ((show Prop from (t49 (M := M) (a0)))) (e4) (e8)
  have v1 := p2144 (M := M) (a0)
  have v2 := ((v0) (v1))
  have v3 := fun z0 : M => fun z1 : M => p2131 (M := M) z1 z0
  have v4 := fun z0 : M => fun z1 : M => p2015 (M := M) (e13 z0 z1) (e14 z1) (e1 z0) (v3 z0 z1)
  have v5 := fun z0 : M => fun z1 : M => p604 (M := M) (e13 z0 z1) (a0) (e15 z1) (e2 z0) (v4 z0 z1)
  have v6 := fun z0 : M => p593 (M := M) z0 (fun w0 : M => (e16 w0)) (e3 z0) ((fun w0 : M => v5 z0 w0))
  have v7 := fun z0 : M => p2131 (M := M) z0 (e5)
  have v8 := fun z0 : M => p2015 (M := M) (e17 z0) (e14 z0) (e6) (v7 z0)
  have v9 := fun z0 : M => p604 (M := M) (e17 z0) (a0) (e15 z0) (e7) (v8 z0)
  have v10 := p593 (M := M) (e5) (fun w0 : M => (e16 w0)) (e8) ((fun w0 : M => v9 w0))
  have v11 := fun z0 : M => p1543 (M := M) e (e18) z0 (boundPredicate_certificate predicate)
  have v12 : (∀ z0 : M, (e21 z0)) := (show (∀ z0 : M, (e21 z0)) from v11)
  have v13 := fun z0 : M => p153 (e19 z0) (e20) (e8) (v10) (v12 z0)
  have v14 := fun z0 : M => p156 (e3 z0) (e19 z0) (e8) (v6 z0) (v13 z0)
  have v15 := p339 (M := M) (fun w0 : M => (e3 w0)) (e8) ((fun w0 : M => v14 w0))
  have v16 := fun z0 : M => p2131 (M := M) z0 (e5)
  have v17 := fun z0 : M => p2015 (M := M) (e22 z0) (e1 z0) (e6) (v16 z0)
  have v18 := fun z0 : M => p604 (M := M) (e22 z0) (a0) (e2 z0) (e7) (v17 z0)
  have v19 := p445 (M := M) (e5) (fun w0 : M => (e3 w0)) (e8) ((fun w0 : M => v18 w0))
  have v20 := p112 (e4) (e8) (v15) (v19)
  have v21 := ((v2) (v20))
  exact v21
-- Actual MMB 2148 sizess1
theorem p2148 (e : Nat → M) (a0 : (M → Prop)) (a1 : M) (predicate : ZF209.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0)))  : (t0 (t18 (M := M) (a0) (t120 (t124 (a1)))) (t47 (M := M) (t125 (a0)) (a1))) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : M := (t124 u0)
  let e2  : M := (t124 (a1))
  let e3 (u0 : M) : (M → Prop) := (t120 (e1 u0))
  let e4  : (M → Prop) := (t120 (e2))
  let e5 (u0 : M) : Prop := (t18 (M := M) (a0) (e3 u0))
  let e6  : Prop := (t18 (M := M) (a0) (e4))
  let e7  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e5 x0_0)))
  let e8  : Prop := (t16 (M := M) (a1) (e7))
  let e10  : Prop := (t47 (M := M) ((show M from (t125 (a0)))) (a1))
  let e11  : Prop := (t0 (e8) (e10))
  have v0 := fun z0 : M => p2131 (M := M) z0 (a1)
  have v1 := fun z0 : M => p2015 (M := M) (e0 z0) (e1 z0) (e2) (v0 z0)
  have v2 := fun z0 : M => p604 (M := M) (e0 z0) (a0) (e3 z0) (e4) (v1 z0)
  have v3 := p593 (M := M) (a1) (fun w0 : M => (e5 w0)) (e6) ((fun w0 : M => v2 w0))
  have v4 := p1544 (M := M) e (e7) (a1) (boundPredicate_certificate predicate)
  have v5 : (e11) := (show (e11) from v4)
  have v6 := p156 (e6) (e8) (e10) (v3) (v5)
  exact v6
-- Actual MMB 2149 sizess
theorem p2149 (e : Nat → M) (a0 : (M → Prop)) (a1 : M) (predicate : ZF209.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0)))  : (t0 (t49 (M := M) (a0)) (t3 (t18 (M := M) (a0) (t120 (t124 (a1)))) (t47 (M := M) (t125 (a0)) (a1)))) := by
  let e0  : Prop := (t49 (M := M) (a0))
  let e2  : (M → Prop) := (t120 ((show M from (t124 (a1)))))
  let e3  : Prop := (t18 (M := M) (a0) (e2))
  let e4  : M := (t125 (a0))
  let e5  : Prop := (t47 (M := M) (e4) (a1))
  let e8  : (M → Prop) := (t120 ((show M from (t124 (e4)))))
  let e10  : Prop := (t18 (M := M) (e8) (e2))
  have v0 := p2148 (M := M) e (a0) (a1) predicate
  have v1 := p4 (e0) ((show Prop from (t0 (e3) (e5)))) (v0)
  have v2 := p2140 (M := M) (e4) (a1)
  have v3 := p2147 (M := M) e (a0) predicate
  have v4 := p610 (M := M) (a0) (e8) (e2)
  have v5 := p155 (e0) ((show Prop from (t18 (M := M) (a0) (e8)))) ((show Prop from (t0 (e10) (e3)))) (v3) (v4)
  have v6 := p162 (e0) (e5) (e10) (e3) (v2) (v5)
  have v7 := p113 (e0) (e3) (e5) (v1) (v6)
  exact v7
-- Actual MMB 2150 sizeupto
theorem p2150 (a0 : M)  : (t10 (M := M) (t125 (t120 (t124 (a0)))) (a0)) := by
  let e0  : M := (t124 (a0))
  let e1  : (M → Prop) := (t120 (e0))
  let e2  : M := (t125 (e1))
  let e12  : Prop := (t18 (M := M) (e1) ((show (M → Prop) from (t120 ((show M from (t124 (e2))))))))
  let ee : Nat → M := fun _ => t124 a0
  have v0 := p875 (M := M) (e2) (a0)
  have v1 := p2149 (M := M) ee (e1) (a0) (literalBitAt_certificate ee 0)
  have v2 := p2090 (M := M) (e0)
  have v3 := ((v1) (v2))
  have v4 := p609 (M := M) (e1)
  have v5 := p117 ((show Prop from (t18 (M := M) (e1) (e1)))) ((show Prop from (t47 (M := M) (e2) (a0)))) (v3) (v4)
  have v6 := ((v0) (v5))
  have v7 := p2140 (M := M) (a0) (e2)
  have v8 := p2147 (M := M) ee (e1) (literalBitAt_certificate ee 0)
  have v9 := p117 ((show Prop from (t49 (M := M) (e1)))) (e12) (v8) (v2)
  have v10 := p117 (e12) ((show Prop from (t47 (M := M) (a0) (e2)))) (v7) (v9)
  have v11 := ((v6) (v10))
  exact v11

end ZF209.MM0ModelReplay
