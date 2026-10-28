import Mathlib

/-! # Half Frame Scalar Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HalfFrameScalarComparison.CM

/-! Eliminate the common nonzero half-frame constant from a natural
line multiplier. -/

theorem ratio (k₀ k₁ h₀ h₁ s₀ s₁ c a l : ℂ)
    (hk₀ : k₀ ≠ 0) (hk₁ : k₁ ≠ 0) (hh₀ : h₀ ≠ 0) (hh₁ : h₁ ≠ 0)
    (hs₀ : s₀ ≠ 0) (hc : c ≠ 0)
    (h₀eq : k₀ * h₀ = c * s₀) (h₁eq : k₁ * h₁ = c * s₁)
    (ha : a * k₀ / k₁ = l) : a = l * h₀ / h₁ * s₁ / s₀ := by
  have hk0 : k₀ = c * s₀ / h₀ := (eq_div_iff hh₀).mpr h₀eq
  have hk1 : k₁ = c * s₁ / h₁ := (eq_div_iff hh₁).mpr h₁eq
  have he : a = l * k₁ / k₀ := (eq_div_iff hk₀).mpr ((div_eq_iff hk₁).mp ha)
  rw [he, hk0, hk1]
  field_simp

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HalfFrameScalarComparison.CM
