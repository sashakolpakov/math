import OAI.Analysis.PDE.Elliptic.Boundary.Third.Holder
import OAI.Analysis.PDE.Nonlinear.HolderComponents

/-! Tangential third derivatives and the recovered pure-normal entry
control the complete third derivative tensor, including its oscillation. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Nonlinear

variable {I : Type*} [Fintype I] [DecidableEq I]

local instance boundaryThirdTensorFirstGroup : NormedAddCommGroup
    (EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance boundaryThirdTensorFirstSpace : NormedSpace ℝ
    (EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance boundaryThirdTensorSecondGroup : NormedAddCommGroup
    (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance boundaryThirdTensorSecondSpace : NormedSpace ℝ
    (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance

theorem trilinear_norm_le_of_coordinate_bound
    (T : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ)
    {M : ℝ}
    (h : ∀ i j k, |T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
      (EuclideanSpace.single k 1)| ≤ M) :
    ‖T‖ ≤ (Fintype.card I : ℝ)^3 * M := by
  calc
    ‖T‖ ≤ ∑ i, ‖T (EuclideanSpace.single i 1)‖ := by
      simpa only [EuclideanSpace.basisFun_apply] using
        OAI.Analysis.PDE.Nonlinear.clm_norm_le_sum_basis (EuclideanSpace.basisFun I ℝ) T
    _ ≤ ∑ _i : I, ∑ _j : I, ∑ _k : I, M := by
      apply Finset.sum_le_sum
      intro i _
      have h₁ := OAI.Analysis.PDE.Nonlinear.clm_norm_le_sum_basis (EuclideanSpace.basisFun I ℝ) (T (EuclideanSpace.single i 1))
      simp only [EuclideanSpace.basisFun_apply] at h₁
      apply h₁.trans
      apply Finset.sum_le_sum
      intro j _
      have h₂ := OAI.Analysis.PDE.Nonlinear.clm_norm_le_sum_basis (EuclideanSpace.basisFun I ℝ)
        (T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      simp only [EuclideanSpace.basisFun_apply] at h₂
      apply h₂.trans
      apply Finset.sum_le_sum
      intro k _
      simpa only [EuclideanSpace.basisFun_apply, Real.norm_eq_abs] using h i j k
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem third_difference_le_of_tangential_and_normal
    {u : EuclideanSpace ℝ I → ℝ} (hu : ContDiff ℝ 3 u)
    (k : I) (x y : EuclideanSpace ℝ I) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (htan : ∀ i, i ≠ k →
      ‖fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x -
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) y‖ ≤ M)
    (hnormal : |fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))) x
          (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) -
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))) y
          (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)| ≤ N) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
      (Fintype.card I : ℝ)^3 * (M+N) := by
  have hentry (i) (hi : i ≠ k) (a b : I) :
      |fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) -
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) y
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)| ≤ M := by
    let D := fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x -
      fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) y
    have hD := (D (EuclideanSpace.single a 1)).le_opNorm (EuclideanSpace.single b 1)
    have hD' := D.le_opNorm (EuclideanSpace.single a 1)
    have he : ‖D (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)‖ ≤ ‖D‖ := by
      simpa using hD.trans (mul_le_mul_of_nonneg_right hD' (norm_nonneg _))
    exact (show _ ≤ ‖D‖ from he).trans (htan i hi)
  apply trilinear_norm_le_of_coordinate_bound
  intro i a b
  simp only [sub_apply, OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian u hu]
  by_cases hi : i = k
  · subst i
    by_cases ha : a = k
    · subst a
      by_cases hb : b = k
      · subst b
        exact hnormal.trans (le_add_of_nonneg_left hM)
      · rw [hessian_directional_cycle hu (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)
            (EuclideanSpace.single b 1) x |>.symm,
          hessian_directional_cycle hu (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)
            (EuclideanSpace.single b 1) y |>.symm]
        exact (hentry b hb k k).trans (le_add_of_nonneg_right hN)
    · rw [hessian_directional_cycle hu (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
          (EuclideanSpace.single k 1) x,
        hessian_directional_cycle hu (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
          (EuclideanSpace.single k 1) y]
      exact (hentry a ha b k).trans (le_add_of_nonneg_right hN)
  · exact (hentry i hi a b).trans (le_add_of_nonneg_right hN)

theorem third_norm_le_of_tangential_and_normal
    {u : EuclideanSpace ℝ I → ℝ} (hu : ContDiff ℝ 3 u)
    (k : I) (x : EuclideanSpace ℝ I) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (htan : ∀ i, i ≠ k →
      ‖fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x‖ ≤ M)
    (hnormal : |fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))) x
          (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)| ≤ N) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ (Fintype.card I : ℝ)^3 * (M+N) := by
  have hentry (i) (hi : i ≠ k) (a b : I) :
      |fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)| ≤ M := by
    let D := fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x
    have hD := (D (EuclideanSpace.single a 1)).le_opNorm (EuclideanSpace.single b 1)
    have hD' := D.le_opNorm (EuclideanSpace.single a 1)
    have he : ‖D (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)‖ ≤ ‖D‖ := by
      simpa using hD.trans (mul_le_mul_of_nonneg_right hD' (norm_nonneg _))
    exact (show _ ≤ ‖D‖ from he).trans (htan i hi)
  apply trilinear_norm_le_of_coordinate_bound
  intro i a b
  simp only [OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian u hu]
  by_cases hi : i = k
  · subst i
    by_cases ha : a = k
    · subst a
      by_cases hb : b = k
      · subst b
        exact hnormal.trans (le_add_of_nonneg_left hM)
      · rw [hessian_directional_cycle hu (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)
            (EuclideanSpace.single b 1) x |>.symm]
        exact (hentry b hb k k).trans (le_add_of_nonneg_right hN)
    · rw [hessian_directional_cycle hu (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
          (EuclideanSpace.single k 1) x]
      exact (hentry a ha b k).trans (le_add_of_nonneg_right hN)
  · exact (hentry i hi a b).trans (le_add_of_nonneg_right hN)

end OAI.Analysis.PDE.Elliptic
