module
public import ModelReplay2210
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2255 rlameqs
theorem p2255 (e : Nat → M) (a1 : M → M) (a2 : M → M) (graph : ZF207.MM0ModelPeano.FunctionGraphCertificate e 1 (fun v => a2 (v 0)))  : (∀ z0 : M, (t17 (M := M) (t120 (t135 (M := M) (a1 z0) (fun x2_0 : M => (a2 x2_0)))) (t81 (M := M) (t82 (M := M) (fun x2_0 : M => (a2 x2_0))) (t120 (a1 z0))))) := by
  let e1 (u0 : M) : (M → Prop) := (t120 (a1 u0))
  let e2 (u0 : M) : (M → Prop) := (t81 (M := M) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (a2 x0_0))))) (e1 u0))
  let e3 (u0 : M) : M := (t135 (M := M) (a1 u0) (fun x0_0 : M => (a2 x0_0)))
  let e4 (u0 : M) : (M → Prop) := (t120 (e3 u0))
  let e5 (u0 : M) : Prop := (t49 (M := M) (e2 u0))
  let e6 (u0 : M) : Prop := (t17 (M := M) (e2 u0) (e4 u0))
  let e7 (u0 : M) : Prop := (t3 (e5 u0) (e6 u0))
  let e8 (u0 : M) : Prop := (t49 (M := M) (e1 u0))
  let e9 (u0 : M) : Prop := (t17 (M := M) (e4 u0) (e2 u0))
  let ee (x : M) : Nat → M := fun i => Nat.casesOn i (a1 x) e
  let restrictionCertificate (x : M) : ZF207.MM0ModelPeano.FormulaCertificate (ee x) 1 (fun v => e2 x (v 0)) :=
    literalRestrictedGraph_certificate (literalBitAt_certificate (ee x) 0) (graph.prependParameter (a1 x))
  have v0 := fun z0 : M => p555 (M := M) (e2 z0) (e4 z0)
  have v1 := fun z0 : M => p2094 (M := M) (ee z0) (e2 z0) (restrictionCertificate z0)
  have v2 : (∀ z0 : M, (e7 z0)) := (show (∀ z0 : M, (e7 z0)) from v1)
  have v3 := fun z0 : M => p1450 (M := M) e (fun w0 : M => (e1 w0)) (fun w0 : M => (a2 w0)) graph z0
  have v4 := fun z0 : M => p2090 (M := M) (a1 z0)
  have v5 := fun z0 : M => b3 (e8 z0) (e5 z0) (v3 z0) (v4 z0)
  have v6 := fun z0 : M => p117 (e5 z0) (e6 z0) (v2 z0) (v5 z0)
  have v7 := fun z0 : M => b3 (e6 z0) (e9 z0) (v0 z0) (v6 z0)
  exact v7
-- Actual MMB 2256 elrlam

end ZF207.MM0ModelReplay
