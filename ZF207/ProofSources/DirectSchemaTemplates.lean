module
public import DirectFormulaTemplate
@[expose] public section
namespace RosserDirect.SchemaTemplates
open Turing Segment FourStack FormulaTemplate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

def sepSuffix := payloadBits [7,0,2,3,11,7,13,15,13] ++ [.frameEnd]
def sepMiddle := payloadBits [7,11,0,4,3]
def sepPrefix := tokenBits 1 ++ payloadBits [0,2,3,0,4,3]
def separationProgram : List Cmd :=
 [.literal sepSuffix,.copy,.literal sepMiddle,.copy,.literal sepPrefix,.drop]

def repSuffix := payloadBits [7,15,0,2,3,11,7,13,15,13,11] ++ [.frameEnd]
def repMiddle := payloadBits [7,15,11,0,6,3]
def repBridge := payloadBits [2,0,5,11,11,13,13,13,0,2,3,0,6,3]
def replacementProgram : List Cmd :=
 [.literal repSuffix,.copy,.literal repMiddle,.copy,.drop,.literal repBridge,.copy,.drop,.copy,.drop,.literal (tokenBits 1)]

theorem separation (body : ZFR.Formula) (v : Option Symbol) (p tail out : List Symbol) :
 TM2.Reaches (FormulaTemplate.machine separationProgram)
  (cfg4 (.run 0) v p (TypedContext.value (.formula body) ++ tail) [] out)
  (cfg4 .done none p tail [] (TypedContext.value (.formula (ZFR.separationFormula body)) ++ out)) := by
 have h0 := FormulaTemplate.literal separationProgram 0 (sepSuffix) rfl v p (TypedContext.value (.formula body) ++ tail) (out)
 have h1 := FormulaTemplate.copy separationProgram 1 rfl body none p (tail) ((sepSuffix) ++ (out))
 have h2 := FormulaTemplate.literal separationProgram 2 (sepMiddle) rfl none p (TypedContext.value (.formula body) ++ tail) (payloadBits (ZFR.TokenVM.emitFormula body) ++ ((sepSuffix) ++ (out)))
 have h3 := FormulaTemplate.copy separationProgram 3 rfl body none p (tail) ((sepMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula body) ++ ((sepSuffix) ++ (out))))
 have h4 := FormulaTemplate.literal separationProgram 4 (sepPrefix) rfl none p (TypedContext.value (.formula body) ++ tail) (payloadBits (ZFR.TokenVM.emitFormula body) ++ ((sepMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula body) ++ ((sepSuffix) ++ (out)))))
 have h5 := FormulaTemplate.drop separationProgram 5 rfl body none p (tail) ((sepPrefix) ++ (payloadBits (ZFR.TokenVM.emitFormula body) ++ ((sepMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula body) ++ ((sepSuffix) ++ (out))))))
 have h6 := FormulaTemplate.finish separationProgram 6 rfl none p (tail) ((sepPrefix) ++ (payloadBits (ZFR.TokenVM.emitFormula body) ++ ((sepMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula body) ++ ((sepSuffix) ++ (out))))))
 simp only [TM2.Reaches,List.append_assoc] at *
 have h := h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6))))))
 simpa [TM2.Reaches,TypedContext.value,valueSymbols,valueTokens,ZFR.separationFormula,ZFR.replacementFormula,ZFR.functionalityFormula,ZFR.sourceIff,ZFR.TokenVM.emitFormula,ZFR.TokenVM.emitNat,payloadBits,sepSuffix,sepMiddle,sepPrefix,repSuffix,repMiddle,repBridge,List.flatMap_append,List.append_assoc] using h

theorem replacement (c b a : ZFR.Formula) (v : Option Symbol) (p tail out : List Symbol) :
 TM2.Reaches (FormulaTemplate.machine replacementProgram)
  (cfg4 (.run 0) v p (TypedContext.value (.formula c) ++ TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ tail) [] out)
  (cfg4 .done none p tail [] (TypedContext.value (.formula (ZFR.replacementFormula a b c)) ++ out)) := by
 have h0 := FormulaTemplate.literal replacementProgram 0 (repSuffix) rfl v p (TypedContext.value (.formula c) ++ TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ tail) (out)
 have h1 := FormulaTemplate.copy replacementProgram 1 rfl c none p (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ tail) ((repSuffix) ++ (out))
 have h2 := FormulaTemplate.literal replacementProgram 2 (repMiddle) rfl none p (TypedContext.value (.formula c) ++ TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ tail) (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repSuffix) ++ (out)))
 have h3 := FormulaTemplate.copy replacementProgram 3 rfl c none p (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ tail) ((repMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repSuffix) ++ (out))))
 have h4 := FormulaTemplate.drop replacementProgram 4 rfl c none p (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ tail) (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repSuffix) ++ (out)))))
 have h5 := FormulaTemplate.literal replacementProgram 5 (repBridge) rfl none p (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ tail) (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repSuffix) ++ (out)))))
 have h6 := FormulaTemplate.copy replacementProgram 6 rfl b none p (TypedContext.value (.formula a) ++ tail) ((repBridge) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repSuffix) ++ (out))))))
 have h7 := FormulaTemplate.drop replacementProgram 7 rfl b none p (TypedContext.value (.formula a) ++ tail) (payloadBits (ZFR.TokenVM.emitFormula b) ++ ((repBridge) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repSuffix) ++ (out)))))))
 have h8 := FormulaTemplate.copy replacementProgram 8 rfl a none p (tail) (payloadBits (ZFR.TokenVM.emitFormula b) ++ ((repBridge) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repSuffix) ++ (out)))))))
 have h9 := FormulaTemplate.drop replacementProgram 9 rfl a none p (tail) (payloadBits (ZFR.TokenVM.emitFormula a) ++ (payloadBits (ZFR.TokenVM.emitFormula b) ++ ((repBridge) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repSuffix) ++ (out))))))))
 have h10 := FormulaTemplate.literal replacementProgram 10 (tokenBits 1) rfl none p (tail) (payloadBits (ZFR.TokenVM.emitFormula a) ++ (payloadBits (ZFR.TokenVM.emitFormula b) ++ ((repBridge) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repSuffix) ++ (out))))))))
 have h11 := FormulaTemplate.finish replacementProgram 11 rfl none p (tail) ((tokenBits 1) ++ (payloadBits (ZFR.TokenVM.emitFormula a) ++ (payloadBits (ZFR.TokenVM.emitFormula b) ++ ((repBridge) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repMiddle) ++ (payloadBits (ZFR.TokenVM.emitFormula c) ++ ((repSuffix) ++ (out)))))))))
 simp only [TM2.Reaches,List.append_assoc] at *
 have h := h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9.trans (h10.trans (h11)))))))))))
 simpa [TM2.Reaches,TypedContext.value,valueSymbols,valueTokens,ZFR.separationFormula,ZFR.replacementFormula,ZFR.functionalityFormula,ZFR.sourceIff,ZFR.TokenVM.emitFormula,ZFR.TokenVM.emitNat,payloadBits,sepSuffix,sepMiddle,sepPrefix,repSuffix,repMiddle,repBridge,List.flatMap_append,List.append_assoc] using h

end RosserDirect.SchemaTemplates
