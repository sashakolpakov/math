import OAI.AlgebraicGeometry.CycleClass.Thom.Betti

/-! # Bilinear Support Sum -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BilinearSupportSum.Constructions

noncomputable section

/-! Bilinear comparison requires equality only for the support pairs
actually occurring with nonzero coefficients in the given cycles. -/

open scoped BigOperators

variable {ι κ M : Type} [AddCommGroup M] [Module ℚ M]

theorem bilinear_apply_support_sum
    (F : (ι →₀ ℚ) →ₗ[ℚ] (κ →₀ ℚ) →ₗ[ℚ] M) (a : ι →₀ ℚ) (b : κ →₀ ℚ) :
    F a b = ∑ i ∈ a.support, ∑ j ∈ b.support, (a i * b j) • F (Finsupp.single i 1) (Finsupp.single j 1) := by
  classical
  have ha : a = ∑ i ∈ a.support, a i • Finsupp.single i (1 : ℚ) := by
    simpa only [Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one] using (Finsupp.sum_single a).symm
  have hb : b = ∑ j ∈ b.support, b j • Finsupp.single j (1 : ℚ) := by
    simpa only [Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one] using (Finsupp.sum_single b).symm
  conv_lhs => rw [ha, hb]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

theorem bilinear_apply_eq_of_support_pairs
    (F G : (ι →₀ ℚ) →ₗ[ℚ] (κ →₀ ℚ) →ₗ[ℚ] M) (a : ι →₀ ℚ) (b : κ →₀ ℚ)
    (h : ∀ i ∈ a.support, ∀ j ∈ b.support,
      F (Finsupp.single i 1) (Finsupp.single j 1) = G (Finsupp.single i 1) (Finsupp.single j 1)) :
    F a b = G a b := by
  rw [bilinear_apply_support_sum F a b, bilinear_apply_support_sum G a b]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [h i hi j hj]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BilinearSupportSum.Constructions
