import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup
import Mathlib.Algebra.Group.Hom.Basic

/-! # Shear Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.ShearClasses

/-! Algebra of a symmetric bilinear pairing on commutative groups under
an integer shear. These identities apply to the actual Poincare pair classes. -/
variable {H G : Type*} [CommGroup H] [CommGroup G]

theorem bilinear_shear_cross (B : H →* (H →* G)) (x y : H) (t : ℤ) :
    B (x * y ^ t) y = B x y * B y y ^ t := by
  rw [B.map_mul]
  change B x y * B (y ^ t) y = _
  have h := congrArg (fun f : H →* G => f y) (B.map_zpow y t)
  exact congrArg (fun z => B x y * z) h

theorem symmetric_bilinear_shear_square (B : H →* (H →* G))
    (hs : ∀ x y, B x y = B y x) (x y : H) (t : ℤ) :
    B (x * y ^ t) (x * y ^ t) = B x x * B y y ^ (t ^ 2) * B x y ^ (2 * t) := by
  have hy (z : H) : B (y ^ t) z = B y z ^ t :=
    congrArg (fun f : H →* G => f z) (B.map_zpow y t)
  calc
    _ = (B x x * B x y ^ t) * (B y x ^ t * (B y y ^ t) ^ t) := by
      rw [B.map_mul]
      change B x (x * y ^ t) * B (y ^ t) (x * y ^ t) = _
      rw [(B x).map_mul, (B x).map_zpow, hy, (B y).map_mul, (B y).map_zpow, mul_zpow]
    _ = B x x * B y y ^ (t ^ 2) * (B x y ^ t * B x y ^ t) := by
      have hp : (B y y ^ t) ^ t = B y y ^ (t ^ 2) :=
        (zpow_mul (B y y) t t).symm.trans (congrArg (fun n : ℤ => B y y ^ n) (pow_two t).symm)
      rw [hs y x, hp]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = _ := by rw [← zpow_add, ← two_mul]

theorem shear_three_class_powers (L M B : G) (a b c t : ℤ) :
    (L * M ^ (t ^ 2) * B ^ (2 * t)) ^ a * M ^ b * (B * M ^ t) ^ c =
      L ^ a * M ^ (b + t * c + t ^ 2 * a) * B ^ (c + 2 * t * a) := by
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  simp only [mul_assoc, mul_left_comm, mul_comm]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.ShearClasses
