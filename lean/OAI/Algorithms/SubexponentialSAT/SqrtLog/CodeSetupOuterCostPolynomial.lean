import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCostNative

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupOuterCost

/-- The exact four-stage accounting pattern used by the outer constructor. -/
def staged (W p l g z : ℕ) : ℕ :=
  let cp := 10000*(W+p+2)
  let cl := 10000*(W+cp+l+1)
  let cg := 10000*(W+cp+cl+g+1)
  cp+cl+cg+10000*(W+cp+cl+cg+z+1)

theorem staged_le (W p l g z : ℕ) :
    staged W p l g z ≤ 10001^4*(W+p+l+g+z+2) := by
  unfold staged
  norm_num
  omega

/-- Serializer normal form, with the number of vertices as a separate input. -/
def serialRow (r D b Ld Lm : ℕ) : ℕ :=
  7*D+35*(D*r)+D*(2000*(r+Ld+Lm+b+D+4)^2+2)+2*D+4*(D*b)+23

def serial (N r D t b Ld Lm : ℕ) : ℕ :=
  N*(2*(35*(t*D)+7*t+t*(serialRow r D b Ld Lm+2)+13)+8*r+10)+13*r+18

theorem serial_le (N r D t b Ld Lm Z : ℕ)
    (hN : N ≤ Z) (hr : r ≤ Z) (hD : D ≤ Z) (ht : t ≤ Z)
    (hb : b ≤ Z) (hd : Ld ≤ Z) (hm : Lm ≤ Z) :
    serial N r D t b Ld Lm ≤ 10000000*(Z+1)^6 := by
  calc
    _ ≤ serial Z Z Z Z Z Z Z := by unfold serial serialRow; gcongr
    _ ≤ _ := by unfold serial serialRow; ring_nf; omega

theorem sum_input_le_product (m W : ℕ) :
    m+W+16 ≤ (m+16)*(W+1) := by nlinarith

theorem word_bound (W ql Dl : ℕ)
    (hq : ql ≤ 2*W+11) (hD : Dl ≤ 6*W+30) :
    max ql Dl+1 ≤ 31*(W+1) := by omega

end SubexponentialSAT.SqrtLog.CodeSetupOuterCost

end OAI.Algorithms
