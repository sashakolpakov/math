import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MollificationDerivatives

/-! Lower-order interpolation obtained by differentiating a positive mollifier. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem smoothData_hessian_kernel {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (x v w : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (fderiv ℝ (smoothData φ u)) x v w =
      ∫ y, fderiv ℝ (fderiv ℝ (φ.normed volume)) y w v * u (x - y) := by
  rw [second_fderiv_smoothData φ u hu huc]
  have hg : ContDiff ℝ 2 (fun y => u (x - y)) := hu.comp (contDiff_const.sub contDiff_id)
  have hgc := huc.comp_homeomorph (Homeomorph.subLeft x)
  have h := integral_mul_second_fderiv_compact (φ.normed volume) (fun y => u (x - y))
    φ.contDiff_normed hg hgc v w
  simpa only [smoothData, scalarConvolution, second_fderiv_reflect_translate u hu] using h

theorem mollifier_hessian_integrable {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (v w : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun y => fderiv ℝ (fderiv ℝ (φ.normed volume)) y v w) := by
  have hK : ContDiff ℝ 2 (φ.normed volume) := φ.contDiff_normed
  have hD : ContDiff ℝ 1 (fderiv ℝ (φ.normed volume)) := hK.fderiv_right (by norm_num)
  exact ((hD.continuous_fderiv one_ne_zero).clm_apply continuous_const |>.clm_apply continuous_const).integrable_of_hasCompactSupport
    (((φ.hasCompactSupport_normed.fderiv ℝ).fderiv_apply ℝ v).comp_left
      (g := fun L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ => L w) (by simp))

theorem mollifier_hessian_bound {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    {M : ℝ} (_ : 0 ≤ M) (hbound : ∀ x, |u x| ≤ M) (x v w : EuclideanSpace ℝ (Fin m)) :
    |fderiv ℝ (fderiv ℝ (smoothData φ u)) x v w| ≤
      M * ∫ y, |fderiv ℝ (fderiv ℝ (φ.normed volume)) y w v| := by
  rw [smoothData_hessian_kernel φ u hu huc, ← Real.norm_eq_abs]
  have hb : ∀ᵐ y, ‖fderiv ℝ (fderiv ℝ (φ.normed volume)) y w v * u (x - y)‖ ≤
      M * |fderiv ℝ (fderiv ℝ (φ.normed volume)) y w v| := by
    filter_upwards with y
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbound _) (abs_nonneg _)
  have hi := (mollifier_hessian_integrable φ w v).norm.const_mul M
  have hi' : Integrable (fun y => M * |fderiv ℝ (fderiv ℝ (φ.normed volume)) y w v|) := by
    simpa only [Real.norm_eq_abs] using hi
  have h := norm_integral_le_of_norm_le hi' hb
  simpa only [integral_const_mul, Real.norm_eq_abs] using h

theorem hessian_interpolation_mollifier {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    {α : ℝ} (hα : 0 ≤ α) :
    ∃ B ≥ 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      ∀ H M, 0 ≤ H → 0 ≤ M → (∀ x, |u x| ≤ M) →
      (∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) →
      ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ (m : ℝ) * m * φ.rOut ^ α * H + B * M := by
  let B : ℝ := ∑ i : Fin m, ∑ j : Fin m, ∫ y,
    |fderiv ℝ (fderiv ℝ (φ.normed volume)) y (EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ))|
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => integral_nonneg fun y => abs_nonneg _
  refine ⟨B, hB, ?_⟩
  intro u hu huc H M hH hM hbound hh x
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hentry (i j : Fin m) : |fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| ≤ H * φ.rOut ^ α +
      M * ∫ y, |fderiv ℝ (fderiv ℝ (φ.normed volume)) y
        (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))| := by
    let v : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i (1 : ℝ)
    let w : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single j (1 : ℝ)
    have hh' (a b : EuclideanSpace ℝ (Fin m)) :
        |fderiv ℝ (fderiv ℝ u) a v w - fderiv ℝ (fderiv ℝ u) b v w| ≤ H * ‖a - b‖ ^ α :=
      (euclidean_bilinear_entry_le_norm (fderiv ℝ (fderiv ℝ u) a - fderiv ℝ (fderiv ℝ u) b) i j).trans (hh a b)
    have he := smoothData_error φ (fun y => fderiv ℝ (fderiv ℝ u) y v w)
      ((hD.continuous_fderiv one_ne_zero).clm_apply continuous_const |>.clm_apply continuous_const) hH hα hh' x
    rw [← second_fderiv_smoothData φ u hu huc x v w] at he
    have hb := mollifier_hessian_bound φ u hu huc hM hbound x v w
    have ht' := abs_add_le (fderiv ℝ (fderiv ℝ u) x v w - fderiv ℝ (fderiv ℝ (smoothData φ u)) x v w)
      (fderiv ℝ (fderiv ℝ (smoothData φ u)) x v w)
    rw [sub_add_cancel, abs_sub_comm] at ht'
    exact ht'.trans (add_le_add he hb)
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, |fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| := euclidean_bilinear_norm_le_sum _
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, (H * φ.rOut ^ α + M * ∫ y,
        |fderiv ℝ (fderiv ℝ (φ.normed volume)) y (EuclideanSpace.single j (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ))|) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, B]; ring

theorem hessian_interpolation {m : ℕ} {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ B > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      ∀ H M, 0 ≤ H → 0 ≤ M → (∀ x, |u x| ≤ M) →
      (∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) →
      ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ε * H + B * M := by
  have ht : Tendsto (fun k => (m : ℝ) * m * (standardMollifier m k).rOut ^ α) atTop (𝓝 0) := by
    simpa using ((standardMollifier_radius_tendsto m).rpow_const_nhds_zero hα).const_mul ((m : ℝ) * m)
  obtain ⟨k, hk⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  obtain ⟨B, hB, hb⟩ := hessian_interpolation_mollifier (standardMollifier m k) hα.le
  refine ⟨B + 1, by linarith, ?_⟩
  intro u hu huc H M hH hM hbound hh x
  exact (hb u hu huc H M hH hM hbound hh x).trans
    (add_le_add (mul_le_mul_of_nonneg_right hk.le hH) (mul_le_mul_of_nonneg_right (by linarith) hM))

end OAI.Analysis.PDE.Schauder
