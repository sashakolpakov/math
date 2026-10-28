import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Sharp

/-! Coordinate estimates imply a genuine operator-norm Schauder estimate. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem euclidean_bilinear_entry_le_norm {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (i j : Fin m) :
    |A (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| ≤ ‖A‖ := by
  have h := (A (EuclideanSpace.single i (1 : ℝ))).le_opNorm (EuclideanSpace.single j (1 : ℝ))
  have h' := A.le_opNorm (EuclideanSpace.single i (1 : ℝ))
  simpa using h.trans (mul_le_mul_of_nonneg_right h' (norm_nonneg _))

theorem euclidean_bilinear_expansion {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (v w : EuclideanSpace ℝ (Fin m)) :
    A v w = ∑ i : Fin m, ∑ j : Fin m, (v i * w j) *
      A (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
  have hv : (∑ i : Fin m, v i • EuclideanSpace.single i (1 : ℝ)) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
  have hw : (∑ j : Fin m, w j • EuclideanSpace.single j (1 : ℝ)) = w := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr w
  calc
    _ = A (∑ i : Fin m, v i • EuclideanSpace.single i (1 : ℝ))
        (∑ j : Fin m, w j • EuclideanSpace.single j (1 : ℝ)) := by rw [hv, hw]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem euclidean_bilinear_norm_le_sum {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ i : Fin m, ∑ j : Fin m,
      |A (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [euclidean_bilinear_expansion, Real.norm_eq_abs]
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin m,
        |(v i * w j) * A (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin m, ∑ j : Fin m,
        |A (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| * ‖v‖ * ‖w‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul]
      have hv : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
      have hw : |w j| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w j
      nlinarith [mul_le_mul hv hw (abs_nonneg (w j)) (norm_nonneg v),
        abs_nonneg (A (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)))]
    _ = _ := by simp only [Finset.sum_mul]

theorem newtonianPotential_hessian_holder {m : ℕ} (hm : 2 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ),
      ContDiff ℝ 2 f → HasCompactSupport f → ∀ H, 0 ≤ H →
      (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) → ∀ x z,
      ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) z -
        fderiv ℝ (fderiv ℝ (newtonianPotential f)) x‖ ≤ C * H * ‖z - x‖ ^ α := by
  choose C hC hbound using newtonianPotential_hessian_entry_holder hm hα hα1
  have hsum : 0 ≤ ∑ i, ∑ j, C i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => (hC i j).le
  refine ⟨(∑ i, ∑ j, C i j) + 1, by linarith, ?_⟩
  intro f hf hfc H hH hh x z
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin m,
        |(fderiv ℝ (fderiv ℝ (newtonianPotential f)) z -
          fderiv ℝ (fderiv ℝ (newtonianPotential f)) x)
          (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| :=
      euclidean_bilinear_norm_le_sum _
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, C i j * H * ‖z - x‖ ^ α := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simpa using hbound i j f hf hfc H hH hh x z
    _ = (∑ i, ∑ j, C i j) * H * ‖z - x‖ ^ α := by simp only [Finset.sum_mul]
    _ ≤ ((∑ i, ∑ j, C i j) + 1) * H * ‖z - x‖ ^ α := by
      gcongr
      linarith

end OAI.Analysis.PDE.Schauder
