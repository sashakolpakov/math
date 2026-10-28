import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup
import Mathlib.Algebra.Group.Hom.Basic

/-! # Diagonal Power Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.DiagonalPowerRecovery

/-! Diagonal powers of a symmetric bilinear pairing determine its mixed
pairings up to the corresponding doubled power. -/
variable {H G : Type*} [CommGroup H] [CommGroup G]

theorem symmetric_bilinear_diagonal_product (B : H →* (H →* G))
    (hs : ∀ x y, B x y = B y x) (x y : H) :
    B (x * y) (x * y) = B x x * B y y * B x y ^ 2 := by
  rw [B.map_mul]
  change B x (x * y) * B y (x * y) = _
  rw [(B x).map_mul, (B y).map_mul, hs y x, pow_two]
  ac_rfl

theorem symmetric_bilinear_pair_power_of_diagonal_power
    (B C : H →* (H →* G)) (hB : ∀ x y, B x y = B y x) (hC : ∀ x y, C x y = C y x)
    (d : ℕ) (hd : ∀ x, B x x ^ d = C x x ^ d) (x y : H) :
    B x y ^ (2 * d) = C x y ^ (2 * d) := by
  have h := hd (x * y)
  rw [symmetric_bilinear_diagonal_product B hB,
    symmetric_bilinear_diagonal_product C hC, mul_pow, mul_pow, mul_pow, mul_pow,
    hd x, hd y] at h
  have hp := mul_left_cancel h
  simpa only [← pow_mul] using hp

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.DiagonalPowerRecovery
