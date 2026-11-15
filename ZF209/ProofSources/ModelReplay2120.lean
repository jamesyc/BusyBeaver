module
public import ModelReplay2094
public import ModelLiteralBitParameterCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2095 ellower
theorem p2095 (e : Nat → M) (a0 : (M → Prop)) (a1 : M) (predicate : ZF209.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0)))  : (t0 (t49 (M := M) (a0)) (t3 (t16 (M := M) (a1) (t120 (t121 (a0)))) (t16 (M := M) (a1) (a0)))) := by
  let e0  : Prop := (t49 (M := M) (a0))
  let e2  : (M → Prop) := (t120 ((show M from (t121 (a0)))))
  let e3  : Prop := (t17 (M := M) (a0) (e2))
  have v0 := p104 (e0) (e3)
  have v1 := p2094 (M := M) e (a0) predicate
  have v2 := b3 ((show Prop from (t3 (e0) (e3)))) ((show Prop from (t0 (e0) (e3)))) (v0) (v1)
  have v3 := p575 (M := M) (e0) (a1) (a0) (e2) (v2)
  have v4 := p144 (e0) ((show Prop from (t16 (M := M) (a1) (a0)))) ((show Prop from (t16 (M := M) (a1) (e2)))) (v3)
  exact v4
-- Actual MMB 2096 lowerns
theorem p2096 (a0 : M)  : (t10 (M := M) (t121 (t120 (a0))) (a0)) := by
  let e0  : (M → Prop) := (t120 (a0))
  let e1  : M := (t121 (e0))
  let e4  : Prop := (t17 (M := M) (e0) ((show (M → Prop) from (t120 (e1)))))
  let e5  : Prop := (t10 (M := M) (a0) (e1))
  let ee : Nat → M := fun _ => a0
  have v0 := p341 (M := M) (a0) (e1)
  have v1 := p2041 (M := M) (a0) (e1)
  have v2 := p2094 (M := M) ee (e0) (literalBitAt_certificate ee 0)
  have v3 := p2090 (M := M) (a0)
  have v4 := p117 ((show Prop from (t49 (M := M) (e0)))) (e4) (v2) (v3)
  have v5 := b3 (e4) (e5) (v1) (v4)
  have v6 := b3 (e5) ((show Prop from (t10 (M := M) (e1) (a0)))) (v0) (v5)
  exact v6
-- Actual MMB 2097 eqlower1
theorem p2097 (e : Nat → M) (a0 : (M → Prop)) (a1 : M) (predicate : ZF209.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0)))  : (t0 (t49 (M := M) (a0)) (t3 (t17 (M := M) (a0) (t120 (a1))) (t10 (M := M) (t121 (a0)) (a1)))) := by
  let e0  : (M → Prop) := (t120 (a1))
  let e1  : Prop := (t17 (M := M) (a0) (e0))
  let e2  : M := (t121 (a0))
  let e4  : Prop := (t49 (M := M) (a0))
  let e5  : Prop := (t10 (M := M) (e2) (a1))
  let e6  : Prop := (t2 (e4) (e5))
  let e7  : (M → Prop) := (t120 (e2))
  have v0 := p2096 (M := M) (a1)
  have v1 := p2092 (M := M) (a0) (e0)
  have v2 := p362 (M := M) (e1) (e2) ((show M from (t121 (e0)))) (a1) (v0) (v1)
  have v3 := p63 (e4) (e1) (e5) (v2)
  have v4 := p2094 (M := M) e (a0) predicate
  have v5 := p53 (e4) (e5)
  have v6 := p153 (e6) (e4) ((show Prop from (t17 (M := M) (a0) (e7)))) (v4) (v5)
  have v7 := p54 (e4) (e5)
  have v8 := p2015 (M := M) (e6) (e2) (a1) (v7)
  have v9 := p564 (M := M) (a0) (e7) (e0) (e6) (v6) (v8)
  have v10 := p114 (e4) (e1) (e5) (v3) (v9)
  exact v10
-- Actual MMB 2098 eqlower2
theorem p2098 (e : Nat → M) (a0 : (M → Prop)) (a1 : M) (predicate : ZF209.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0)))  : (t0 (t49 (M := M) (a0)) (t3 (t17 (M := M) (t120 (a1)) (a0)) (t10 (M := M) (a1) (t121 (a0))))) := by
  let e0  : (M → Prop) := (t120 (a1))
  let e1  : M := (t121 (a0))
  have v0 := p556 (M := M) (e0) (a0)
  have v1 := p345 (M := M) (a1) (e1)
  have v2 := p2097 (M := M) e (a0) (a1) predicate
  have v3 := p172 ((show Prop from (t49 (M := M) (a0)))) ((show Prop from (t17 (M := M) (a0) (e0)))) ((show Prop from (t10 (M := M) (e1) (a1)))) ((show Prop from (t17 (M := M) (e0) (a0)))) ((show Prop from (t10 (M := M) (a1) (e1)))) (v0) (v1) (v2)
  exact v3
-- Actual MMB 2099 lowerinj
theorem p2104 (a0 : M) (a1 : M)  : (t3 (t16 (M := M) (a0) (t120 (t122 (M := M) (a1)))) (t10 (M := M) (a0) (a1))) := by
  let e4  : Prop := (t3 ((show Prop from (t16 (M := M) (a0) ((show (M → Prop) from (t120 ((show M from (t122 (M := M) (a1)))))))))) ((show Prop from (t10 (M := M) (a0) (a1)))))
  have v0 := p2089 (M := M) (a0) (a1)
  have v1 : (e4) := (show (e4) from v0)
  exact v1
-- Actual MMB 2105 snid
theorem p2115 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t10 (M := M) (a3) (a4)))) : (t0 (a0) (t10 (M := M) (t123 (a1) (a3)) (t123 (a2) (a4)))) := by
  let e0  : (M → Prop) := (t120 (a3))
  let e1  : (M → Prop) := (t120 (a4))
  let e2 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e3 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e4 (u0 : M) : Prop := (t16 (M := M) u0 (e0))
  let e5 (u0 : M) : Prop := (t16 (M := M) u0 (e1))
  let e6 (u0 : M) : Prop := (t4 (e2 u0) (e4 u0))
  let e7 (u0 : M) : Prop := (t4 (e3 u0) (e5 u0))
  let e13  : Prop := (t0 (a0) ((show Prop from (t10 (M := M) ((show M from (t123 (a1) (a3)))) ((show M from (t123 (a2) (a4))))))))
  have v0 := fun z0 : M => p349 (M := M) (a0) z0 (a1) (a2) (h0)
  have v1 := p2015 (M := M) (a0) (a3) (a4) (h1)
  have v2 := fun z0 : M => p575 (M := M) (a0) z0 (e0) (e1) (v1)
  have v3 := fun z0 : M => p243 (a0) (e2 z0) (e3 z0) (e4 z0) (e5 z0) (v0 z0) (v2 z0)
  have v4 := p584 (M := M) (a0) (fun w1 : M => (e6 w1)) (fun w1 : M => (e7 w1)) ((fun w1 : M => v3 w1))
  have v5 := p2091 (M := M) (a0) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e6 x0_0))))) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e7 x0_0))))) (v4)
  have v6 : (e13) := (show (e13) from v5)
  exact v6
-- Actual MMB 2116 inseq

end ZF209.MM0ModelReplay
