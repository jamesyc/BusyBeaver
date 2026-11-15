module
public import QuantifierTemplates
@[expose] public section
namespace ZFR

theorem nd_double_negation (Γ : Context) (p : Formula) :
 ND (.seq Γ (.imp (.imp (.imp p .bot) .bot) p)) := by
 apply ND.ii
 apply ND.ie (ND.pc _ p .bot)
 apply ND.ii
 apply ND.exp
 exact ND.ie (a := .imp p .bot) (ND.ctx (by simp)) (ND.ctx (by simp))

end ZFR
