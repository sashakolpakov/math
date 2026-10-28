import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup
import Mathlib.Algebra.Group.Hom.Basic

/-! # Opposite Translations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.OppositeTranslations

/-! Opposite translations cancel the mixed terms of any bilinear pairing
with values in a commutative group. Symmetry of the pairing is unnecessary. -/
variable {H G : Type*} [CommGroup H] [CommGroup G]

theorem bilinear_opposite_translation_diagonal (B : H →* (H →* G)) (x y : H) :
    B (y * x) (y * x) * B (y⁻¹ * x) (y⁻¹ * x) = B x x ^ 2 * B y y ^ 2 := by
  have hy (z : H) : B y⁻¹ z = (B y z)⁻¹ :=
    congrArg (fun f : H →* G => f z) (B.map_inv y)
  have hp : B (y * x) (y * x) = (B y y * B y x) * (B x y * B x x) := by
    rw [B.map_mul]
    change B y (y * x) * B x (y * x) = _
    rw [(B y).map_mul, (B x).map_mul]
  have hm : B (y⁻¹ * x) (y⁻¹ * x) =
      (B y y * (B y x)⁻¹) * ((B x y)⁻¹ * B x x) := by
    rw [B.map_mul]
    change B y⁻¹ (y⁻¹ * x) * B x (y⁻¹ * x) = _
    rw [hy, (B y).map_mul, (B y).map_inv, (B x).map_mul, (B x).map_inv,
      mul_inv_rev, inv_inv]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [hp, hm]
  calc
    _ = (B x x * B x x) * (B y y * B y y) *
        (B y x * (B y x)⁻¹) * (B x y * (B x y)⁻¹) := by ac_rfl
    _ = B x x ^ 2 * B y y ^ 2 := by simp [pow_two]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.OppositeTranslations
