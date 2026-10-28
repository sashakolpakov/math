import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryArithmetic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT LeafParametersProgram

/-- Keep the ring instance abstract while forming the query certificate. -/
def DenominatorIdentity (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (u : RingProgram.ScalarCode 3 (m.val 33)) (R : ℕ) : Prop :=
  (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
    (LayoutDenominatorProgramQuery.value (m.val 33) (IrreducibleSearch.data hd) M cache u R) *
      (2 : (IrreducibleSearch.data hd).O (m.val 33)) ^ (R-1)=1

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
