import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProductBounds

namespace OAI.Algorithms

/-! Numerical polynomial envelopes for the native hash-row program.
HashCircuitProgramCost relates these expressions to actual execution. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost
open MomentsProgram

/-- Bit length of a normalized dictionary with at most S retained keys. -/
def bytesBound (B d n u J S : ℕ) : ℕ := S*(2*(n+u+J)+2*(d*B)+2)
def scaleBound (B d n u J S : ℕ) : ℕ :=
  S*(40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+22*(n+u+J)+57)+5
def normalizeBound (B d n u J S : ℕ) : ℕ :=
  S*(220*(2*S+1)*(n+u+J+d*B+1)+Dictionary.codeBranchBudget B d+2)+1
def productBound (B d n u J S : ℕ) : ℕ :=
  S*(Product.stepEnvelope B d n u J (S*S) S+2)+1
def fetchBound (n P : ℕ) : ℕ := n*(44*n+31*P+58)+2*n+16
def negativeBound (B d n u J S : ℕ) : ℕ :=
  52*bytesBound B d n u J S+18*(d*B)+9*d+
    scaleBound B d n u J S+normalizeBound B d n u J S+73
def literalBound (B d n u J S : ℕ) : ℕ :=
  let P := bytesBound B d n u J S
  8*n+16+fetchBound n P+9*P+10+negativeBound B d n u J S+1+
    29*P+productBound B d n u J S+29+3
def payloadBound (B d n k : ℕ) : ℕ := 2*(d*B)+2+(4*n+4)*k
def rowBound (B d n u J S k : ℕ) : ℕ :=
  let P := bytesBound B d n u J S
  3*payloadBound B d n k+6*(d*B)+8+(7*P+5)+
    (3+k*(6*(2*n+1)+literalBound B d n u J S+7))+
    (54*P+14*(d*B)+9*d+scaleBound B d n u J S+normalizeBound B d n u J S+74)+3
def programBound (B d n u J S k m : ℕ) : ℕ :=
  7+m*(6*payloadBound B d n k+rowBound B d n u J S k+7)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost

end OAI.Algorithms
