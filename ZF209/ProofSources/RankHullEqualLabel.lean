module
public import RankHullSourceSchemas
@[expose] public section
namespace ZFR

def separatedSpec (s b : Nat) (phi : Formula) : Formula := .all
 (sourceIff (.mem 0 (b+1)) (.and (.mem 0 (s+1)) phi))

theorem nd_separated_instance {Γ : Context} (s b : Nat) (phi : Formula)
 (h : ND (.seq Γ (separatedSpec s b phi))) (i : Nat) :
 ND (.seq Γ (sourceIff (.mem i b) (.and (.mem i s) (subst i phi)))) := by
 simpa [separatedSpec, sourceIff, subst, rename, lift, substMap] using ND.allE i h

end ZFR
