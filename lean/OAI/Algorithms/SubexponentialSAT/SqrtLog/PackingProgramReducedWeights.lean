import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramWeights

namespace OAI.Algorithms

/-! Exact cancellation of the common q^4 factor in incremental head scores.
This removes q from the two runtime weights when epsilon is 1/s. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram

 def reducedScore (n s M r ci overlap : ℕ) : ℕ :=
  (n*s)^2*ci + 8*(M*r)^2*overlap

 theorem reducedScore_identity (n s M r q ci overlap constant : ℕ) :
    (n^2*(s*q^2)^2)*ci + (M^2*(2*r)^2)*(constant+2*q^4*overlap) =
      (M^2*(2*r)^2)*constant + q^4*reducedScore n s M r ci overlap := by
  unfold reducedScore
  ring

 theorem reducedScore_order (n s M r q ci cj hi hj constant : ℕ) (hq : 0 < q) :
    (n^2*(s*q^2)^2)*ci + (M^2*(2*r)^2)*(constant+2*q^4*hi) ≤
      (n^2*(s*q^2)^2)*cj + (M^2*(2*r)^2)*(constant+2*q^4*hj) ↔
    reducedScore n s M r ci hi ≤ reducedScore n s M r cj hj := by
  rw [reducedScore_identity, reducedScore_identity, Nat.add_le_add_iff_left]
  constructor
  · intro h
    exact Nat.le_of_mul_le_mul_left h (pow_pos hq 4)
  · exact Nat.mul_le_mul_left _

 theorem reducedScore_weights (n s M r ci overlap : ℕ) :
    reducedScore n s M r ci overlap = (n^2*s^2)*ci + (8*M^2*r^2)*overlap := by
  unfold reducedScore
  ring

 theorem reducedScore_bound (n s M r ci overlap C H : ℕ) (hc : ci ≤ C) (hh : overlap ≤ H) :
    reducedScore n s M r ci overlap ≤ (n*s)^2*C + 8*(M*r)^2*H := by
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hc) (Nat.mul_le_mul_left _ hh)

 theorem reducedScore_scaled (n s M r q ci overlap : ℕ) :
    (n^2*(s*q^2)^2)*ci + (2*q^4*(M^2*(2*r)^2))*overlap =
      q^4*reducedScore n s M r ci overlap := by
  unfold reducedScore
  ring

 theorem reducedScore_scaled_order (n s M r q ci cj hi hj : ℕ) (hq : 0 < q) :
    (n^2*(s*q^2)^2)*ci + (2*q^4*(M^2*(2*r)^2))*hi ≤
      (n^2*(s*q^2)^2)*cj + (2*q^4*(M^2*(2*r)^2))*hj ↔
    reducedScore n s M r ci hi ≤ reducedScore n s M r cj hj := by
  rw [reducedScore_scaled,reducedScore_scaled]
  constructor
  · intro h
    exact Nat.le_of_mul_le_mul_left h (pow_pos hq 4)
  · exact Nat.mul_le_mul_left _

 theorem order_of_rational_offset (a b x y : ℕ) (constant scale : ℚ) (hs : 0 < scale)
    (ha : (a : ℚ) = constant + scale*x) (hb : (b : ℚ) = constant + scale*y) :
    a ≤ b ↔ x ≤ y := by
  have h : (a : ℚ) ≤ b ↔ (x : ℚ) ≤ y := by
    rw [ha, hb, add_le_add_iff_left]
    exact mul_le_mul_iff_right₀ hs
  exact_mod_cast h

 theorem reducedScore_rational_identity (n s M r q ci overlap : ℕ) (constant : ℚ) :
    ((n^2*(s*q^2)^2 : ℕ) : ℚ)*ci + ((M^2*(2*r)^2 : ℕ) : ℚ)*
      (constant+2*(q : ℚ)^4*overlap) =
    ((M^2*(2*r)^2 : ℕ) : ℚ)*constant + (q : ℚ)^4*reducedScore n s M r ci overlap := by
  unfold reducedScore
  push_cast
  ring
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
