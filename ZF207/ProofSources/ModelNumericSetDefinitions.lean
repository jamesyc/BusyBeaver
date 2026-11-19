module
public import ModelReplay1999
public import LiteralSourcePredicateDefinitions
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def t122 (a0 : M)  : M := (t117 (M := M) (t31 (M := M)) (a0))
noncomputable def t132 (a0 : M) (a1 : (M → Prop))  : M := (t121 (M := M) (t19 (M := M) (t120 (M := M) (a0)) (a1)))
noncomputable def t135 (a1 : M) (a2 : M → M)  : M := (t121 (M := M) (t81 (M := M) (t82 (M := M) (fun x2_0 : M => (a2 x2_0))) (t120 (M := M) (a1))))
noncomputable def t146 (a0 : (M → Prop))  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (t145 (M := M) (a0) x0_0)))
noncomputable def t147 (a0 : M)  : M := (t142 (M := M) (t28 (M := M)) (t89 (M := M) (fun x1_0 : M => (t89 (M := M) (fun x2_0 : M => (t82 (M := M) (fun x3_0 : M => (t29 (M := M) x3_0))))))) (a0))
noncomputable def t149 (a0 : M) (a1 : M)  : M := (t142 (M := M) (a1) (t89 (M := M) (fun x1_0 : M => (t89 (M := M) (fun x2_0 : M => (t82 (M := M) (fun x3_0 : M => (t131 (M := M) x1_0 x3_0))))))) (a0))
noncomputable def t150 (a0 : M) (a1 : M)  : M := (t149 (M := M) (a0) (t131 (M := M) (a1) (t28 (M := M))))
noncomputable def t151 (a0 : M)  : M := (t142 (M := M) (t28 (M := M)) (t89 (M := M) (fun x1_0 : M => (t89 (M := M) (fun x2_0 : M => (t82 (M := M) (fun x3_0 : M => (t135 (M := M) (t124 (M := M) (t29 (M := M) (t125 (M := M) (t76 (M := M) (t120 (M := M) x3_0))))) (fun x4_0 : M => (t50 (M := M) (t10 (M := M) x4_0 (t28 (M := M))) x1_0 (t84 (M := M) (t120 (M := M) x3_0) (t46 (M := M) x4_0 (t30 (M := M))))))))))))) (a0))
noncomputable def t152 (a0 : M) (a1 : M)  : M := (t50 (M := M) (t48 (M := M) (a0) (t147 (M := M) (a1))) (t29 (M := M) (t84 (M := M) (t120 (M := M) (t151 (M := M) (a1))) (a0))) (t28 (M := M)))
noncomputable def t153 (a0 : M) (a1 : M)  : M := (t110 (M := M) (t28 (M := M)) (t82 (M := M) (fun x1_0 : M => (t131 (M := M) (a0) x1_0))) (a1))

end ZF207.MM0ModelReplay
