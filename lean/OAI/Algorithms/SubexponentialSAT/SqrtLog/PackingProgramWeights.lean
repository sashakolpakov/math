import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramScores

namespace OAI.Algorithms

/-! Explicit positive denominator and bit bounds for the two rational weights. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram

def Weights.ofFractions (xn xd yn yd : ℕ) (hxd : 0 < xd) (hyd : 0 < yd) : Weights where
  incidence := yn^2 * xd^2
  head := xn^2 * yd^2
  denominator := xd^2 * yd^2
  denominator_pos := Nat.mul_pos (pow_pos hxd _) (pow_pos hyd _)

theorem Weights.ofFractions_incidence (xn xd yn yd : ℕ) (hxd : 0 < xd) (hyd : 0 < yd) :
    ((yn : ℚ)/yd)^2 =
      ((Weights.ofFractions xn xd yn yd hxd hyd).incidence : ℚ) /
        (Weights.ofFractions xn xd yn yd hxd hyd).denominator := by
  have hx : (xd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hxd
  have hy : (yd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hyd
  simp only [Weights.ofFractions, Nat.cast_mul, Nat.cast_pow]
  field_simp


theorem Weights.ofFractions_head (xn xd yn yd : ℕ) (hxd : 0 < xd) (hyd : 0 < yd) :
    ((xn : ℚ)/xd)^2 =
      ((Weights.ofFractions xn xd yn yd hxd hyd).head : ℚ) /
        (Weights.ofFractions xn xd yn yd hxd hyd).denominator := by
  have hx : (xd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hxd
  have hy : (yd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hyd
  simp only [Weights.ofFractions, Nat.cast_mul, Nat.cast_pow]
  field_simp


theorem Weights.ofFractions_bound (xn xd yn yd B : ℕ) (hxd : 0 < xd) (hyd : 0 < yd)
    (hxn : xn ≤ B) (hx : xd ≤ B) (hyn : yn ≤ B) (hy : yd ≤ B) :
    (Weights.ofFractions xn xd yn yd hxd hyd).incidence +
      (Weights.ofFractions xn xd yn yd hxd hyd).head ≤ 2 * B^4 := by
  dsimp [Weights.ofFractions]
  have h1 : yn^2 * xd^2 ≤ B^4 := by
    calc
      _ ≤ B^2 * B^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hyn _) (Nat.pow_le_pow_left hx _)
      _ = _ := by ring
  have h2 : xn^2 * yd^2 ≤ B^4 := by
    calc
      _ ≤ B^2 * B^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hxn _) (Nat.pow_le_pow_left hy _)
      _ = _ := by ring
  omega

/-- A coarse but uniform bit bound; it is logarithmic in all numerical data. -/
theorem numerator_bitSize_bound (z T W q : ℕ) (h : z ≤ T*(W*q^4)) :
    z.size ≤ T.size + W.size + 4*q.size + 1 := by
  apply Nat.size_le.mpr
  have hT := (Nat.lt_size_self T).le
  have hW := (Nat.lt_size_self W).le
  have hq := (Nat.lt_size_self q).le
  have hp : T*(W*q^4) ≤ 2^(T.size+W.size+4*q.size) := by
    calc
      _ ≤ (2^T.size)*((2^W.size)*(2^q.size)^4) :=
        Nat.mul_le_mul hT (Nat.mul_le_mul hW (Nat.pow_le_pow_left hq _))
      _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1 ; omega
  exact (h.trans hp).trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
