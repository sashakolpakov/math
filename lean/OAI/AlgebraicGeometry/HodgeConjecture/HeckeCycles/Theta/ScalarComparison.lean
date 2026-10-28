import Mathlib

/-! # Scalar Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.ScalarComparison.CM

/-! Scalar assembly for theta covariance under a change of frame. -/

theorem covariance (a c s₀ s₁ q₀ q₁ qn qs t : ℂ) (hs : s₀ ≠ 0)
    (ha : a = c * s₁ / s₀) (hq : q₀ * qn = qs * q₁) :
    a * (qn * (s₀ * (q₀ * t))) = s₁ * (q₁ * (c * (qs * t))) := by
  calc
    _ = c * s₁ * (q₀ * qn) * t := by rw [ha]; field_simp
    _ = _ := by rw [hq]; ring

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.ScalarComparison.CM
