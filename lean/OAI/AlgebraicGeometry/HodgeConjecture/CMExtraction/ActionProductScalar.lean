import Mathlib

/-! # Action Product Scalar -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActionProductScalar.TestTransport

/-! A fixed first factor and a scalar second factor give the same scalar on their product. -/

variable {G K V : Type*} [Group G] [Semiring K] [AddCommMonoid V] [Module K V]

theorem action_product_scalar (ρ : G →* (V ≃ₗ[K] V)) (a b g : G)
    (hg : a * b = g) (v : V) (c : K)
    (ha : ρ a v = v) (hb : ρ b v = c • v) : ρ g v = c • v := by
  rw [← hg, map_mul, LinearEquiv.mul_apply, hb, map_smul, ha]

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActionProductScalar.TestTransport
