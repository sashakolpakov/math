import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-! # Wedge -/

namespace OAI.Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing

noncomputable section

/-!
PolarizedPairing: the actual coordinate determinant for the canonical-bundle wedge.
Rows are `dz₁,...,dzₙ,dbar(z₁),...,dbar(zₙ)` and columns are
`∂x₁,...,∂xₙ,∂y₁,...,∂yₙ`. The sign converts that column order to the
complex orientation `∂x₁,∂y₁,...,∂xₙ,∂yₙ`.
-/

def canonicalWedgeMatrix (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks 1 (Complex.I • 1) 1 ((-Complex.I) • 1)

theorem canonicalWedgeMatrix_det (n : ℕ) :
    (canonicalWedgeMatrix n).det = (-2 * Complex.I) ^ n := by
  rw [canonicalWedgeMatrix, Matrix.det_fromBlocks_one₁₁, Matrix.one_mul,
    ← sub_smul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  congr 1
  ring

theorem complex_orientation_phase (n : ℕ) :
    (-1 : ℂ) ^ (n * (n - 1) / 2) * (-2 * Complex.I) ^ n =
      (Complex.I ^ (n * n))⁻¹ * (2 : ℂ) ^ n := by
  have heven : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  have htotal : n * (n - 1) + n = n * n := by
    cases n with
    | zero => rfl
    | succ k => simp only [Nat.add_sub_cancel]; ring
  have hi : (-Complex.I) ^ 2 = (-1 : ℂ) := by norm_num
  calc
    (-1 : ℂ) ^ (n * (n - 1) / 2) * (-2 * Complex.I) ^ n =
        (-Complex.I) ^ (2 * (n * (n - 1) / 2)) *
          ((2 : ℂ) ^ n * (-Complex.I) ^ n) := by
      rw [pow_mul, hi, ← mul_pow]
      congr 2
      ring
    _ = (-Complex.I) ^ (n * n) * (2 : ℂ) ^ n := by
      rw [heven, mul_comm ((2 : ℂ) ^ n) ((-Complex.I) ^ n),
        ← mul_assoc, ← pow_add, htotal]
    _ = (Complex.I ^ (n * n))⁻¹ * (2 : ℂ) ^ n := by
      rw [← inv_pow, Complex.inv_I]

/-- The exterior-product coefficient relative to complex-oriented real volume. -/
def topWedgeCoefficient {n : ℕ} (a b : ℂ) : ℂ :=
  ((-1 : ℂ) ^ (n * (n - 1) / 2) * (canonicalWedgeMatrix n).det) * (a * b)

theorem topWedgeCoefficient_eq {n : ℕ} (a b : ℂ) :
    topWedgeCoefficient (n := n) a b =
      (Complex.I ^ (n * n))⁻¹ * (2 : ℂ) ^ n * (a * b) := by
  rw [topWedgeCoefficient, canonicalWedgeMatrix_det, complex_orientation_phase]

end

end OAI.Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing
