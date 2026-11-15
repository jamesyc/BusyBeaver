module
public import ModelReplay2256
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2257 rlameq2a
theorem p2267 (e : Nat → M) (a1 : M → M) (a2 : M → M) (graph2 : ZF209.MM0ModelPeano.FunctionGraphCertificate e 1 (fun v => a2 (v 0)))  : (∀ z0 : M, (t17 (M := M) (t76 (M := M) (t120 (t135 (M := M) (a1 z0) (fun x3_0 : M => (a2 x3_0))))) (t120 (a1 z0)))) := by
  let e0 (u0 : M) : M := (t135 (M := M) (a1 u0) (fun x0_0 : M => (a2 x0_0)))
  let e1 (u0 : M) : (M → Prop) := (t120 (e0 u0))
  let e2 (u0 : M) : (M → Prop) := (t76 (M := M) (e1 u0))
  let e4 (u0 : M) : (M → Prop) := (t120 (a1 u0))
  let e5 (u0 : M) : (M → Prop) := (t81 (M := M) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (a2 x0_0))))) (e4 u0))
  let e6 (u0 : M) : (M → Prop) := (t76 (M := M) (e5 u0))
  let e7 (u0 : M) : Prop := (t17 (M := M) (e1 u0) (e5 u0))
  let e8 (u0 : M) : Prop := (t17 (M := M) (e2 u0) (e6 u0))
  let e9 (u0 : M) : Prop := (t17 (M := M) (e6 u0) (e4 u0))
  let e10 (u0 : M) : Prop := (t17 (M := M) (e2 u0) (e4 u0))
  let e11 (u0 : M) : Prop := (t0 (e9 u0) (e10 u0))
  have v0 := fun z0 : M => p557 (M := M) (e2 z0) (e6 z0) (e4 z0)
  have v1 := fun z0 : M => p1377 (M := M) (e1 z0) (e5 z0)
  have v2 := fun z0 : M => p2255 (M := M) e (fun w0 : M => (a1 w0)) (fun w0 : M => (a2 w0)) graph2 z0
  have v3 := fun z0 : M => b3 (e7 z0) (e8 z0) (v1 z0) (v2 z0)
  have v4 := fun z0 : M => b3 (e8 z0) (e11 z0) (v0 z0) (v3 z0)
  have v5 := fun z0 : M => p1457 (M := M) (fun w0 : M => (e4 w0)) (fun w0 : M => (a2 w0)) z0
  have v6 := fun z0 : M => b3 (e9 z0) (e10 z0) (v4 z0) (v5 z0)
  exact v6
-- Actual MMB 2268 rnrlam
end ZF209.MM0ModelReplay
