import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.NaturalKernelPoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ExponentFiniteGeneration

/-! # Balanced Natural Exponents -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.BalancedNaturalExponents

noncomputable section

/-! A strictly positive real balancing of a finite integral weight
matrix gives strictly positive natural exponents with exactly equal degrees. -/
open scoped BigOperators Classical _root_.Matrix
universe u

theorem exists_positive_balanced_natural_exponent {κ ι : Type u} [Fintype κ] [Fintype ι]
    (w : κ → ι → ℕ) (c : κ → ℝ) (hc : ∀ k, 0 < c k)
    (hbal : ∀ i j, (∑ k, c k * (w k i : ℝ)) = ∑ k, c k * (w k j : ℝ)) :
    ∃ a : κ → ℕ, (∀ k, 0 < a k) ∧ a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid w := by
  let A : Matrix (ι × ι) κ ℚ := fun ij k => (w k ij.1 : ℚ) - w k ij.2
  have hAc : A.map (algebraMap ℚ ℝ) *ᵥ c = 0 := by
    ext ij
    change (∑ k, algebraMap ℚ ℝ ((w k ij.1 : ℚ) - w k ij.2) * c k) = 0
    simp only [map_sub, map_natCast]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (by simpa only [mul_comm] using hbal ij.1 ij.2)
  obtain ⟨a, ha, hAa⟩ := NaturalKernelPoint.rationalMatrix_positive_natural_kernel_point A c hAc hc
  refine ⟨a, ha, (Balanced.ExponentFiniteGeneration.mem_balancedExponentMonoid_iff w a).mpr ?_⟩
  intro i j
  have h := congrFun hAa (i, j)
  change (∑ k, ((w k i : ℚ) - w k j) * (a k : ℚ)) = 0 at h
  simp_rw [sub_mul, Finset.sum_sub_distrib] at h
  have he : (∑ k, (a k : ℚ) * (w k i : ℚ)) = ∑ k, (a k : ℚ) * (w k j : ℚ) := by
    simpa only [mul_comm] using sub_eq_zero.mp h
  unfold Balanced.ExponentFiniteGeneration.monomialMultiDegree
  exact_mod_cast he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.BalancedNaturalExponents
