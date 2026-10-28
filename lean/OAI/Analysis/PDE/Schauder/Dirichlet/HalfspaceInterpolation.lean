import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Interpolation

/-! One-sided mollification for interpolation on a closed halfspace.
The convolution is centered one kernel radius inward, so no value or
derivative bound on the other side of the boundary is used. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

def inwardMollifierPoint {m : ℕ} (k : Fin m) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  x + R • EuclideanSpace.single k 1

@[simp] theorem inwardMollifierPoint_coordinate {m : ℕ} (k : Fin m) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : inwardMollifierPoint k R x k = x k + R := by
  simp [inwardMollifierPoint]

theorem norm_inwardMollifierPoint_sub {m : ℕ} (k : Fin m) {R : ℝ} (hR : 0 ≤ R)
    (x : EuclideanSpace ℝ (Fin m)) : ‖inwardMollifierPoint k R x - x‖ = R := by
  simp [inwardMollifierPoint, norm_smul, Real.norm_eq_abs, abs_of_nonneg hR]

theorem halfspace_of_near_inwardMollifierPoint {m : ℕ} (k : Fin m) {R : ℝ}
    {x y : EuclideanSpace ℝ (Fin m)} (hx : 0 ≤ x k)
    (hy : ‖y - inwardMollifierPoint k R x‖ ≤ R) : 0 ≤ y k := by
  have hc := (PiLp.norm_apply_le (y - inwardMollifierPoint k R x) k).trans hy
  change ‖y k - inwardMollifierPoint k R x k‖ ≤ R at hc
  rw [inwardMollifierPoint_coordinate, Real.norm_eq_abs] at hc
  have := (abs_le.mp hc).1
  linarith

theorem halfspace_inwardMollifierPoint_sub {m : ℕ} (k : Fin m) {R : ℝ}
    {x y : EuclideanSpace ℝ (Fin m)} (hx : 0 ≤ x k) (hy : ‖y‖ ≤ R) :
    0 ≤ (inwardMollifierPoint k R x - y) k := by
  have hc := (PiLp.norm_apply_le y k).trans hy
  rw [Real.norm_eq_abs] at hc
  have := (abs_le.mp hc).2
  change 0 ≤ inwardMollifierPoint k R x k - y k
  rw [inwardMollifierPoint_coordinate]
  linarith

theorem smoothData_error_halfspace {m : ℕ} (k : Fin m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hh : ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k → |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (x : EuclideanSpace ℝ (Fin m)) (hx : 0 ≤ x k) :
    |smoothData φ f (inwardMollifierPoint k φ.rOut x) - f x| ≤ 2 * H * φ.rOut ^ α := by
  let z := inwardMollifierPoint k φ.rOut x
  have hz : 0 ≤ z k := by dsimp [z]; rw [inwardMollifierPoint_coordinate]; linarith [φ.rOut_pos]
  have herr : |smoothData φ f z - f z| ≤ H * φ.rOut ^ α := by
    have h := φ.dist_normed_convolution_le (μ := volume) hf.aestronglyMeasurable
      (x₀ := z) (ε := H * φ.rOut ^ α) (fun y hy ↦ ?_)
    · simpa only [smoothData, scalarConvolution, convolution_def, ContinuousLinearMap.lsmul_apply,
        smul_eq_mul, dist_eq_norm, Real.norm_eq_abs] using h
    · have hy' : ‖y-z‖ ≤ φ.rOut := by simpa only [mem_ball, dist_eq_norm] using hy.le
      have hyk : 0 ≤ y k := halfspace_of_near_inwardMollifierPoint k hx hy'
      rw [dist_eq_norm, Real.norm_eq_abs]
      exact (hh y hyk z hz).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hy' hα) hH)
  have hzx := hh z hz x hx
  rw [norm_inwardMollifierPoint_sub k φ.rOut_pos.le] at hzx
  have ht := abs_add_le (smoothData φ f z - f z) (f z - f x)
  rw [sub_add_sub_cancel] at ht
  exact ht.trans (by linarith)

theorem mollifier_hessian_bound_halfspace {m : ℕ} (k : Fin m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    {M : ℝ} (_ : 0 ≤ M) (hbound : ∀ x, 0 ≤ x k → |u x| ≤ M)
    (x v w : EuclideanSpace ℝ (Fin m)) (hx : 0 ≤ x k) :
    |fderiv ℝ (fderiv ℝ (smoothData φ u)) (inwardMollifierPoint k φ.rOut x) v w| ≤
      M * ∫ y, |fderiv ℝ (fderiv ℝ (φ.normed volume)) y w v| := by
  rw [smoothData_hessian_kernel φ u hu huc, ← Real.norm_eq_abs]
  have hb : ∀ᵐ y, ‖fderiv ℝ (fderiv ℝ (φ.normed volume)) y w v *
      u (inwardMollifierPoint k φ.rOut x - y)‖ ≤
      M * |fderiv ℝ (fderiv ℝ (φ.normed volume)) y w v| := by
    filter_upwards with y
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) φ.rOut
    · have hyn : ‖y‖ ≤ φ.rOut := by simpa only [mem_closedBall, dist_zero_right] using hy
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (hbound _ (halfspace_inwardMollifierPoint_sub k hx hyn)) (abs_nonneg _)
    · have hy' : y ∉ tsupport (fderiv ℝ (φ.normed volume)) := by
        intro h
        apply hy
        rw [← φ.tsupport_normed_eq (μ := volume)]
        exact tsupport_fderiv_subset ℝ h
      rw [fderiv_of_notMem_tsupport ℝ hy']
      simp
  have hi := (mollifier_hessian_integrable φ w v).norm.const_mul M
  have hi' : Integrable (fun y ↦ M * |fderiv ℝ (fderiv ℝ (φ.normed volume)) y w v|) := by
    simpa only [Real.norm_eq_abs] using hi
  have h := norm_integral_le_of_norm_le hi' hb
  simpa only [integral_const_mul, Real.norm_eq_abs] using h

theorem halfspace_hessian_interpolation_mollifier {m : ℕ} (k : Fin m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) {α : ℝ} (hα : 0 ≤ α) :
    ∃ B ≥ 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      ∀ H M, 0 ≤ H → 0 ≤ M → (∀ x, 0 ≤ x k → |u x| ≤ M) →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x-y‖ ^ α) →
      ∀ x, 0 ≤ x k → ‖fderiv ℝ (fderiv ℝ u) x‖ ≤
        2 * (m : ℝ) * m * φ.rOut ^ α * H + B * M := by
  let B : ℝ := ∑ i : Fin m, ∑ j : Fin m, ∫ y,
    |fderiv ℝ (fderiv ℝ (φ.normed volume)) y (EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ))|
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ integral_nonneg fun y ↦ abs_nonneg _
  refine ⟨B, hB, ?_⟩
  intro u hu huc H M hH hM hbound hh x hx
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hentry (i j : Fin m) : |fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| ≤ 2 * H * φ.rOut ^ α +
      M * ∫ y, |fderiv ℝ (fderiv ℝ (φ.normed volume)) y
        (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))| := by
    let v : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i (1 : ℝ)
    let w : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single j (1 : ℝ)
    have hh' : ∀ a, 0 ≤ a k → ∀ b, 0 ≤ b k →
        |fderiv ℝ (fderiv ℝ u) a v w - fderiv ℝ (fderiv ℝ u) b v w| ≤ H * ‖a-b‖ ^ α := by
      intro a ha b hb
      exact (euclidean_bilinear_entry_le_norm (fderiv ℝ (fderiv ℝ u) a - fderiv ℝ (fderiv ℝ u) b) i j).trans
        (hh a ha b hb)
    have he := smoothData_error_halfspace k φ (fun y ↦ fderiv ℝ (fderiv ℝ u) y v w)
      ((hD.continuous_fderiv one_ne_zero).clm_apply continuous_const |>.clm_apply continuous_const) hH hα hh' x hx
    rw [← second_fderiv_smoothData φ u hu huc _ v w] at he
    have hb := mollifier_hessian_bound_halfspace k φ u hu huc hM hbound x v w hx
    have ht := abs_add_le
      (fderiv ℝ (fderiv ℝ u) x v w - fderiv ℝ (fderiv ℝ (smoothData φ u)) (inwardMollifierPoint k φ.rOut x) v w)
      (fderiv ℝ (fderiv ℝ (smoothData φ u)) (inwardMollifierPoint k φ.rOut x) v w)
    rw [sub_add_cancel, abs_sub_comm] at ht
    exact ht.trans (add_le_add he hb)
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, |fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| := euclidean_bilinear_norm_le_sum _
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, (2 * H * φ.rOut ^ α + M * ∫ y,
        |fderiv ℝ (fderiv ℝ (φ.normed volume)) y (EuclideanSpace.single j (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ))|) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hentry i j
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, B]
      ring

theorem halfspace_hessian_interpolation {m : ℕ} (k : Fin m) {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) :
    ∃ B > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      ∀ H M, 0 ≤ H → 0 ≤ M → (∀ x, 0 ≤ x k → |u x| ≤ M) →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x-y‖ ^ α) →
      ∀ x, 0 ≤ x k → ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ε * H + B * M := by
  have ht : Tendsto (fun j ↦ 2 * (m : ℝ) * m * (standardMollifier m j).rOut ^ α) atTop (𝓝 0) := by
    simpa using ((standardMollifier_radius_tendsto m).rpow_const_nhds_zero hα).const_mul (2 * (m : ℝ) * m)
  obtain ⟨j, hj⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  obtain ⟨B, hB, hb⟩ := halfspace_hessian_interpolation_mollifier k (standardMollifier m j) hα.le
  refine ⟨B+1, by linarith, ?_⟩
  intro u hu huc H M hH hM hbound hh x hx
  exact (hb u hu huc H M hH hM hbound hh x hx).trans
    (add_le_add (mul_le_mul_of_nonneg_right hj.le hH)
      (mul_le_mul_of_nonneg_right (by linarith) hM))

end OAI.Analysis.PDE.Schauder
