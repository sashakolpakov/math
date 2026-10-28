import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic

/-! # Multiplicative Bilinear Parallelogram -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicativeBilinearParallelogram

noncomputable section

/-! The parallelogram identity for a multiplicative bilinear pairing, without assuming inverses in its target monoid. -/

universe u v w

variable {G : Type u} {H : Type v} {C : Type w} [Group G] [Group H] [CommMonoid C]
variable (B : G →* (H →* C))

theorem multiplicativeBilinear_inv_inv (x : G) (a : H) : B x⁻¹ a⁻¹ = B x a := by
  have h₁ : B x a * B x a⁻¹ = 1 := by rw [← (B x).map_mul, mul_inv_cancel, (B x).map_one]
  have h₂ : B x a⁻¹ * B x⁻¹ a⁻¹ = 1 := by
    rw [← MonoidHom.mul_apply, ← B.map_mul, mul_inv_cancel, B.map_one]
    rfl
  calc
    B x⁻¹ a⁻¹ = 1 * B x⁻¹ a⁻¹ := (one_mul _).symm
    _ = (B x a * B x a⁻¹) * B x⁻¹ a⁻¹ := congrArg (fun z => z * B x⁻¹ a⁻¹) h₁.symm
    _ = B x a * (B x a⁻¹ * B x⁻¹ a⁻¹) := mul_assoc _ _ _
    _ = B x a := (congrArg (fun z => B x a * z) h₂).trans (mul_one _)

theorem multiplicativeBilinear_parallelogram (x y : G) (a b : H) :
    B (x * y) (a * b) * B (x * y⁻¹) (a * b⁻¹) = (B x a) ^ 2 * (B y b) ^ 2 := by
  have h₁ : B x b * B x b⁻¹ = 1 := by rw [← (B x).map_mul, mul_inv_cancel, (B x).map_one]
  have h₂ : B y a * B y⁻¹ a = 1 := by
    rw [← MonoidHom.mul_apply, ← B.map_mul, mul_inv_cancel, B.map_one]
    rfl
  calc
    B (x * y) (a * b) * B (x * y⁻¹) (a * b⁻¹) =
        (B x a) ^ 2 * (B y b) ^ 2 * (B x b * B x b⁻¹) * (B y a * B y⁻¹ a) := by
      simp only [map_mul, MonoidHom.mul_apply, multiplicativeBilinear_inv_inv, pow_two]
      simp only [mul_left_comm, mul_comm]
    _ = (B x a) ^ 2 * (B y b) ^ 2 := by rw [h₁, h₂, mul_one, mul_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicativeBilinearParallelogram
