import Mathlib.LinearAlgebra.Dual.Basis

/-! # Balanced Bilinear Eigenvectors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BalancedBilinearEigenvectors

noncomputable section

/-! A balanced bilinear form pairs two eigenspaces only when their
characters match under the given involution. This is the elementary
vanishing needed to restrict the original CM tangent form to its
distinguished pair of character spaces. -/

variable {k V R : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : R → V →ₗ[k] V) (c : R → R) (B : V →ₗ[k] V →ₗ[k] k)
    (hB : ∀ a z w, B (ρ a z) w = B z (ρ (c a) w))

include hB

theorem balancedBilinear_eigen_zero (χ ψ : R → k) (z w : V)
    (hz : ∀ a, ρ a z = χ a • z) (hw : ∀ a, ρ a w = ψ a • w)
    (hne : χ ≠ ψ ∘ c) : B z w = 0 := by
  classical
  by_contra hzw
  apply hne
  funext a
  have he := hB a z w
  rw [hz a, hw (c a), map_smul, LinearMap.smul_apply, map_smul] at he
  exact mul_right_cancel₀ hzw he

theorem balancedBilinear_basis_zero {I : Type*} (b : Module.Basis I k V)
    (χ : I → R → k) (heigen : ∀ i a, ρ a (b i) = χ i a • b i)
    (i j : I) (hne : χ i ≠ χ j ∘ c) : B (b i) (b j) = 0 :=
  balancedBilinear_eigen_zero ρ c B hB (χ i) (χ j) (b i) (b j) (heigen i) (heigen j) hne

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BalancedBilinearEigenvectors
