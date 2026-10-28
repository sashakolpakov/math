import OAI.Analysis.PDE.Concentration.WeightedAverage

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem derivative_weightedBallAverage_nonpos {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x : E) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hΔ : ∀ y ∈ closedBall x R, Δ f y ≤ 0) :
    deriv (weightedBallAverage f x) r ≤ 0 := by
  let g : E → ℝ := fun y => f (x + r • y)
  have hg : ContDiff ℝ 2 g := hf.comp (contDiff_const.add (contDiff_id.const_smul r))
  have hnonpos : (∫ y, meanWeight y * fderiv ℝ g y y) ≤ 0 :=
    mean_radial_derivative_nonpos hg (by
      intro y hy
      change Δ (fun y => f (x + r • y)) y ≤ 0
      rw [laplacian_affine_dilate hf]
      apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hΔ _ _)
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr]
      have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
      exact (mul_le_of_le_one_right hr.le hy').trans hrR)
  have hdg (y : E) : fderiv ℝ g y y = r * fderiv ℝ f (x + r • y) y := by
    have hin : HasFDerivAt (fun z : E => x + r • z) (r • ContinuousLinearMap.id ℝ E) y :=
      (((ContinuousLinearMap.id ℝ E).hasFDerivAt).const_smul r).const_add x
    have h := (hf.differentiable (by norm_num) (x + r • y)).hasFDerivAt.comp y hin
    change HasFDerivAt g _ y at h
    rw [h.fderiv]
    simp
  have he : r * deriv (weightedBallAverage f x) r = ∫ y, meanWeight y * fderiv ℝ g y y := by
    rw [(hasDerivAt_weightedBallAverage hf x r).deriv, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hdg]
    ring
  have hprod : r * deriv (weightedBallAverage f x) r ≤ 0 := he.symm ▸ hnonpos
  nlinarith

/-- A genuine deterministic local supermean inequality for a C² function
whose Laplacian is nonpositive only on the ball in question. -/
theorem weightedBallAverage_le {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x : E) {R : ℝ} (hR : 0 ≤ R) (hΔ : ∀ y ∈ closedBall x R, Δ f y ≤ 0) :
    weightedBallAverage f x R ≤ f x * ∫ y : E, meanWeight y := by
  have hd : Differentiable ℝ (weightedBallAverage f x) :=
    fun r => (hasDerivAt_weightedBallAverage hf x r).differentiableAt
  have hm : AntitoneOn (weightedBallAverage f x) (Icc 0 R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hd.continuous.continuousOn hd.differentiableOn
    intro r hr
    rw [interior_Icc] at hr
    exact derivative_weightedBallAverage_nonpos hf x hr.1 hr.2.le hΔ
  have he : weightedBallAverage f x 0 = f x * ∫ y : E, meanWeight y := by
    simp [weightedBallAverage, integral_const_mul, mul_comm]
  rw [← he]
  exact hm ⟨le_rfl, hR⟩ ⟨hR, le_rfl⟩ hR

/-- The compact positive weight is normalized by its proved positive mass;
thus this is an actual probability average, not an assumed mean operator. -/
theorem normalized_weightedBallAverage_le [Nontrivial E] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (x : E) {R : ℝ} (hR : 0 ≤ R)
    (hΔ : ∀ y ∈ closedBall x R, Δ f y ≤ 0) :
    weightedBallAverage f x R / (∫ y : E, meanWeight y) ≤ f x :=
  (div_le_iff₀ integral_meanWeight_pos).mpr (weightedBallAverage_le hf x hR hΔ)

/-- Only local C² regularity is needed for supermean on a smaller closed ball.
The global representative used in the proof is constructed by a cutoff. -/
theorem weightedBallAverage_le_of_contDiffOn {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (x : E) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hball : closedBall x R ⊆ U) (hΔ : ∀ y ∈ closedBall x r, Δ f y ≤ 0) :
    weightedBallAverage f x r ≤ f x * ∫ y : E, meanWeight y := by
  let β : ContDiffBump x :=
    {rIn := (r + R) / 2, rOut := R, rIn_pos := by linarith,
      rIn_lt_rOut := by linarith}
  let F : E → ℝ := fun y => β y * f y
  have hsupport : tsupport β ⊆ U := by
    rw [β.tsupport_eq]
    exact hball
  have hF : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport β
    · exact β.contDiffAt.mul ((hf y (hsupport hy)).contDiffAt (hU.mem_nhds (hsupport hy)))
    · apply (show ContDiffAt ℝ 2 (fun _ : E => (0 : ℝ)) y from contDiffAt_const).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp [F, hz]
  have he (y : E) (hy : y ∈ closedBall x r) : F =ᶠ[nhds y] f := by
    have hyn : y ∈ ball x β.rIn := by
      change dist y x < (r + R) / 2
      have hy' : dist y x ≤ r := hy
      linarith
    filter_upwards [β.eventuallyEq_one_of_mem_ball hyn] with z hz
    change β z = 1 at hz
    simp [F, hz]
  have hFF : weightedBallAverage F x r = weightedBallAverage f x r := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hw : meanWeight y = 0
    · simp only [hw, zero_mul]
    · have hy : y ∈ closedBall (0 : E) 1 := meanWeight_support (subset_tsupport _ hw)
      have hp : x + r • y ∈ closedBall x r := by
        simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hr]
        have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
        exact mul_le_of_le_one_right hr hy'
      rw [(he _ hp).self_of_nhds]
  have hbound := weightedBallAverage_le hF x hr (fun y hy => by
    rw [(laplacian_congr_nhds (he y hy)).self_of_nhds]
    exact hΔ y hy)
  rw [hFF, (he x (mem_closedBall_self hr)).self_of_nhds] at hbound
  exact hbound

theorem normalized_weightedBallAverage_le_of_contDiffOn [Nontrivial E]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (x : E) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hball : closedBall x R ⊆ U)
    (hΔ : ∀ y ∈ closedBall x r, Δ f y ≤ 0) :
    weightedBallAverage f x r / (∫ y : E, meanWeight y) ≤ f x :=
  (div_le_iff₀ integral_meanWeight_pos).mpr
    (weightedBallAverage_le_of_contDiffOn hU hf x hr hrR hball hΔ)

/-- Harmonic functions have exact weighted means, providing the equality
needed for the logarithmic annulus comparison functions. -/
theorem weightedBallAverage_eq_of_harmonic {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (x : E) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hball : closedBall x R ⊆ U)
    (hΔ : ∀ y ∈ closedBall x r, Δ f y = 0) :
    weightedBallAverage f x r = f x * ∫ y : E, meanWeight y := by
  apply le_antisymm (weightedBallAverage_le_of_contDiffOn hU hf x hr hrR hball
    (fun y hy => (hΔ y hy).le))
  have hneg := weightedBallAverage_le_of_contDiffOn hU hf.neg x hr hrR hball (by
    intro y hy
    change Δ (-f) y ≤ 0
    rw [laplacian_neg]
    simp [hΔ y hy])
  have he : weightedBallAverage (-f) x r = -weightedBallAverage f x r := by
    simp only [weightedBallAverage, Pi.neg_apply, mul_neg, integral_neg]
  change weightedBallAverage (-f) x r ≤ (-f) x * ∫ y : E, meanWeight y at hneg
  rw [he] at hneg
  simp only [Pi.neg_apply, neg_mul] at hneg
  linarith

end OAI.Analysis.PDE.Concentration
