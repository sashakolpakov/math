import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialMatrix

/-! # Polynomial Matrix Components -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialMatrixComponents

noncomputable section

/-! A homogeneous polynomial matrix acts by the usual finite row sums. -/

open _root_.MvPolynomial
universe u v w
variable {R : Type u} [CommRing R] {σ : Type v}
variable {ι κ : Type w} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem homogeneousMatrixColumn_apply (d : ι → ℕ) (e : κ → ℕ)
    (a : ∀ i k, homogeneousSubmodule σ R (e k - d i)) (k : κ) (i : ι) :
    HomogeneousPolynomialMatrix.homogeneousMatrixColumn d e a k i = (a i k).val := rfl

theorem homogeneousPolynomialMatrixMap_apply (d : ι → ℕ) (e : κ → ℕ)
    (a : ∀ i k, homogeneousSubmodule σ R (e k - d i))
    (x : κ →₀ MvPolynomial σ R) (i : ι) :
    HomogeneousPolynomialMatrix.homogeneousPolynomialMatrixMap d e a x i = ∑ k, (a i k).val * x k := by
  classical
  unfold HomogeneousPolynomialMatrix.homogeneousPolynomialMatrixMap
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  · rw [Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finsupp.smul_apply, homogeneousMatrixColumn_apply, smul_eq_mul, mul_comm]
  · intro k
    exact zero_smul _ _

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialMatrixComponents
