import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryDenominatorIdentity

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

/-- Arithmetic execution is indexed by an abstract model, keeping the generated
query model opaque while elaborating the dependent cache fields. -/
structure ArithmeticPreparation (base : Data) (m : Circuit.Model)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34) (W V L : ℕ) where
  out : Data
  ringState : LeafRingSetupProgram.Data
  modulus : SubexpPreparedQuartic.Modulus 3 (m.val 33)
  scalarCache : RingProgram.ScalarCache 3 (m.val 33)
  half : RingProgram.ScalarCode 3 (m.val 33)
  steps : ℕ
  execution : Eval arithmetic steps base out
  time : steps ≤ arithmeticBudget m W V L (base.stacks 740).length
  output : ArithmeticOutput base out m hd modulus scalarCache half ringState
  denominatorInverse : DenominatorIdentity m ht hd modulus scalarCache half (base.stacks 740).length

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
