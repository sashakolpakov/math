import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramCountCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramPolynomialCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyPolynomial

namespace OAI.Algorithms

/-! The complete reconstruction and integer-readback tail is charged by a
fixed polynomial in produced dimensions and actual input-word lengths. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT SubexpLiftRing

def recoveryCoefficient : ℕ := 2400*(ReconstructionProgram.Native.costConstant+1)^4+2100

theorem recoveryBudget_le (Q J t d S : ℕ) (modulus width : List Bool)
    (hQ : Q ≤ S) (hJ : J ≤ S) (ht : t ≤ S) (hd : d ≤ S) (hq : 3^d ≤ S)
    (hm : modulus.length ≤ S) (hw : width.length ≤ S) :
    Count.recoveryBudget Q J t d modulus width ≤ recoveryCoefficient*(S+1)^96 := by
  have hcrt := ReconstructionProgram.Native.budget_polynomial S Q J t d modulus.length width.length
    hQ hJ ht hd hq hm hw
  have hflat : SubexpFlatCount.budget (baseWidth 3 t) modulus
      (List.replicate (d*baseWidth 3 t) false) ≤ 2000*(S+1)^2 := by
    simp only [SubexpFlatCount.budget,RingProgram.ternary_baseWidth,List.length_replicate]
    calc
      _ ≤ 16*(S*(2*S)+2*S+1)+105*(S+2*S+1)^2+1 := by gcongr
      _ ≤ 2000*(S+1)^2 := by nlinarith [Nat.zero_le (S*S)]
  have h2 : (S+1)^2 ≤ (S+1)^96 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : S+1 ≤ (S+1)^96 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (n:=S+1) (by omega) (show 1 ≤ 96 by decide))
  have htail : 6*(modulus.length+baseWidth 3 t)+7+2*modulus.length+2*width.length+6 ≤ 30*(S+1) := by
    simp only [RingProgram.ternary_baseWidth]
    omega
  have hflat' := hflat.trans (Nat.mul_le_mul_left 2000 h2)
  have htail' := htail.trans (Nat.mul_le_mul_left 30 h1)
  have hpos : 1 ≤ (S+1)^96 := Nat.one_le_pow _ _ (by omega)
  change ReconstructionProgram.Native.budget Q J t d modulus.length width.length + 1 +
    SubexpFlatCount.budget (baseWidth 3 t) modulus (List.replicate (d*baseWidth 3 t) false) +
    6*(modulus.length+baseWidth 3 t)+7+2*modulus.length+2*width.length+6 ≤ _
  unfold recoveryCoefficient
  rw [Nat.add_mul]
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms
