module
public import ModelBindParameterCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def t170 (a0 : (M → Prop))  : (M → Prop) := (t82 (M := M) (fun x0_0 : M => (t53 (M := M) (t2 (t51 (M := M) (t69 (M := M) x0_0)) (t16 (t63 (M := M) (t64 (M := M) x0_0) (t68 (M := M) x0_0)) (a0))))))
noncomputable def t171 (a0 : (M → Prop)) (a1 : M)  : M := (t142 (t30) (t170 (M := M) (a0)) (a1))
noncomputable def t172 (a0 : (M → Prop)) (a1 : M)  : Prop := (t51 (M := M) (t171 (M := M) (a0) (a1)))
noncomputable def t173 (a0 : (M → Prop)) (a1 : M) (a2 : M)  : Prop := (t2 (t172 (M := M) (a0) (a1)) (t144 (a2) (a1)))
noncomputable def t174 (a0 : (M → Prop))  : Prop := (t8 (fun x0_0 : M => (t8 (fun x1_0 : M => (t8 (fun x2_0 : M => (t0 (t16 (t63 (M := M) x0_0 x1_0) (a0)) (t16 (t63 (M := M) x0_0 (t149 (M := M) x1_0 x2_0)) (a0)))))))))

end ZF207.MM0ModelReplay
