import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramRow

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

def rowBudgetPolynomial (K L D d B S : ℕ) : ℕ :=
  let T := 2+S*(L+2)
  1000*(2*S+1)^2+S*(K+5*S+3*L+15)+
    300000*(T+1)*(D+1)^3*(d+1)^3*(B+1)^2+
    18*(D*(d*B))+12*S+3*T+67

theorem uniformRowBudget_le_polynomial (N : ℕ) (ps : List (ℕ × ℕ))
    (I K L D d B a b S : ℕ)
    (hN : N ≤ S) (hps : ps.length ≤ S) (hs : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hI : I ≤ S) (ha : a ≤ S) (hb : b ≤ S) :
    uniformRowBudget N ps I K L D d B a b ≤ rowBudgetPolynomial K L D d B S := by
  dsimp only [uniformRowBudget,rowBudgetPolynomial]
  have hT : 2+ps.length*(L+2) ≤ 2+S*(L+2) := by gcongr
  have howner : 1000*((LayoutOwnerFiberProgram.stream ps).length+N+1)^2 ≤
      1000*(2*S+1)^2 := by gcongr ; omega
  have hscan : ps.length*(K+5*I+3*L+15) ≤ S*(K+5*S+3*L+15) := by gcongr
  have hexec : 300000*(2+ps.length*(L+2)+1)*(D+1)^3*(d+1)^3*(B+1)^2 ≤
      300000*(2+S*(L+2)+1)*(D+1)^3*(d+1)^3*(B+1)^2 := by gcongr
  omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
