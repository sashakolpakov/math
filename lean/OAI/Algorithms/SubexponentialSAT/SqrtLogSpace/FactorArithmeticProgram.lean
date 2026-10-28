import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactor

/-! Fixed arithmetic commands used by the specialized assignment evaluator.
Their execution and Good-empty support bounds are proved separately. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram
noncomputable section

def hashArithmetic : Cmd 40 768 :=
  .seq Factor.indicator (.seq (Factor.clear 68) (.seq (Factor.clear 62) Factor.accumulate))

def markedArithmetic : Cmd 40 768 :=
  .seq Clause.caller (.seq (Factor.clear 62) Factor.accumulate)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
