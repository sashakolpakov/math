import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram

namespace OAI.Algorithms

/-! The physical table producer has polynomial cost in the node count,
residue cardinality, precision, and the native ring-operation bounds. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT SubexpLiftRing

theorem budget_le_operations (t d Q : ℕ) :
    budget t d Q+1 ≤ (Q+1)^2 *
      (inverseBudget t d+negativeBudget t d+200*(d*baseWidth 3 t)+200) := by
  unfold budget inverseTableBudget negativeTableBudget differenceTableBudget nodeScanBudget
  ring_nf
  omega

theorem inverseBudget_polynomial (t d : ℕ) :
    inverseBudget t d ≤ 600*(3^d+t+1)*
      (HornerProgram.Services.mulBudget (baseWidth 3 t) d+
        HornerProgram.Services.addBudget (baseWidth 3 t) d+d*baseWidth 3 t+1) := by
  let Km := HornerProgram.Services.mulBudget (baseWidth 3 t) d
  let Ka := HornerProgram.Services.addBudget (baseWidth 3 t) d
  let W := d*baseWidth 3 t
  change (3^d-2+t+1)*(4*Km+4*Ka+300*W+400)+Km+Ka+102*W+113+1 ≤ _
  have hsub : 3^d-2+t+1 ≤ 3^d+t+1 :=
    Nat.add_le_add_right (Nat.add_le_add_right (Nat.sub_le (3^d) 2) t) 1
  have hp := Nat.mul_le_mul_right (4*Km+4*Ka+300*W+400) hsub
  change _ ≤ 600*(3^d+t+1)*(Km+Ka+W+1)
  nlinarith only [hp,Nat.zero_le (3^d*Km),Nat.zero_le (3^d*Ka),Nat.zero_le (3^d*W),
    Nat.zero_le (t*Km),Nat.zero_le (t*Ka),Nat.zero_le (t*W),Nat.zero_le Km,Nat.zero_le Ka,Nat.zero_le W,Nat.zero_le (3^d),Nat.zero_le t]

theorem budget_polynomial (t d Q : ℕ) :
    budget t d Q+1 ≤ 1000*(Q+1)^2*(3^d+t+1)*
      (HornerProgram.Services.mulBudget (baseWidth 3 t) d+
        HornerProgram.Services.addBudget (baseWidth 3 t) d+d*baseWidth 3 t+1) := by
  let Km := HornerProgram.Services.mulBudget (baseWidth 3 t) d
  let Ka := HornerProgram.Services.addBudget (baseWidth 3 t) d
  let W := d*baseWidth 3 t
  have hi := inverseBudget_polynomial t d
  change inverseBudget t d ≤ 600*(3^d+t+1)*(Km+Ka+W+1) at hi
  have hj : negativeBudget t d+200*W+200 ≤ 400*(3^d+t+1)*(Km+Ka+W+1) := by
    change Km+40*W+51+200*W+200 ≤ _
    nlinarith only [Nat.zero_le (3^d*Km),Nat.zero_le (3^d*Ka),Nat.zero_le (3^d*W),
      Nat.zero_le (t*Km),Nat.zero_le (t*Ka),Nat.zero_le (t*W),Nat.zero_le Km,Nat.zero_le Ka,Nat.zero_le W,Nat.zero_le (3^d),Nat.zero_le t]
  have hsum : inverseBudget t d+negativeBudget t d+200*W+200 ≤
      1000*(3^d+t+1)*(Km+Ka+W+1) := by nlinarith only [hi,hj]
  calc budget t d Q+1 ≤ (Q+1)^2*(inverseBudget t d+negativeBudget t d+200*W+200) := budget_le_operations t d Q
    _ ≤ (Q+1)^2*(1000*(3^d+t+1)*(Km+Ka+W+1)) := Nat.mul_le_mul_left _ hsum
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
