module
public import ModelNativeAXPrefixCertificate
public import ModelNativeAXResult
public import ModelNativeCommandBoundary
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeAXSymbolic
open ZFR.ArithmeticRepresentation ZF209.ModelCommands ZF209.MM0ModelReplay ZF209.NativeSource ZF209.NativeCommands
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma initial_spec (t a d h y x tail bottom:M) :
 materialize (valuation t a d h y x) tail bottom initial =
 ⟨t,a,d,h,modelCantor y (modelCantor x tail),bottom⟩ := by rfl
/-- All305 fixed source macros, each valid on arbitrary model-sized values.
This is finite syntax composition, not an external-length substitute for a variable run. -/
theorem native_ax_prefix (n tail t w d h a x y:M) :
 nativeReaches (bodyEntry (.ax a x y) n tail ⟨t,w,d,h⟩)
 (NativeAX.config 4187 n ⟨t330 a (d+x) (h+y),a,d+x,h+y,tail,
 (heads a (d+x) (h+y) d h ++ [t]).foldr modelCantor w⟩) := by
 have hh:=certificate_sound (M:=M) prefix_certificate program_actual n (valuation t a d h y x) tail w
 rw [initial_spec,actual_spec] at hh
 exact hh
end ZF209.NativeAXSymbolic
