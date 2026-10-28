import OAI.Analysis.PDE.Schauder.Calculus.Schauder.KernelDerivative
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Reflection

/-! Smooth even radial cutoffs for the sharp near/far Schauder decomposition. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialCutoff (r : ℝ) (y : E) : ℝ :=
  Real.smoothTransition ((4 - ‖r⁻¹ • y‖ ^ 2) / 3)

theorem contDiff_radialCutoff (r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (radialCutoff (E := E) r) := by
  unfold radialCutoff
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => r⁻¹ • y) := contDiff_id.const_smul _
  have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => ‖r⁻¹ • y‖ ^ 2) := (contDiff_norm_sq ℝ).comp hlin
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => (4 - ‖r⁻¹ • y‖ ^ 2) / 3) :=
    (contDiff_const.sub hsq).div_const 3
  exact Real.smoothTransition.contDiff.comp harg

theorem radialCutoff_nonneg (r : ℝ) (y : E) : 0 ≤ radialCutoff r y := Real.smoothTransition.nonneg _
theorem radialCutoff_le_one (r : ℝ) (y : E) : radialCutoff r y ≤ 1 := Real.smoothTransition.le_one _

theorem radialCutoff_neg (r : ℝ) (y : E) : radialCutoff r (-y) = radialCutoff r y := by
  simp [radialCutoff]

theorem radialCutoff_one {r : ℝ} (hr : 0 < r) {y : E} (hy : ‖y‖ ≤ r) : radialCutoff r y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have he : ‖r⁻¹ • y‖ = ‖y‖ / r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    ring
  rw [he]
  have hq : ‖y‖ / r ≤ 1 := (div_le_one hr).mpr hy
  have hq0 : 0 ≤ ‖y‖ / r := div_nonneg (norm_nonneg _) hr.le
  nlinarith

theorem radialCutoff_zero {r : ℝ} (hr : 0 < r) {y : E} (hy : 2 * r ≤ ‖y‖) : radialCutoff r y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have he : ‖r⁻¹ • y‖ = ‖y‖ / r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    ring
  rw [he]
  have hq : 2 ≤ ‖y‖ / r := (le_div_iff₀ hr).mpr hy
  nlinarith

theorem radialCutoff_unit_rescale (r : ℝ) (y : E) : radialCutoff r y = radialCutoff 1 (r⁻¹ • y) := by
  simp [radialCutoff]

theorem hasCompactSupport_radialCutoff [FiniteDimensional ℝ E] {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (radialCutoff (E := E) r) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (2 * r))
  intro y hy
  have hn : radialCutoff r y ≠ 0 := hy
  simp only [mem_closedBall, dist_zero_right]
  by_contra hh
  exact hn (radialCutoff_zero hr (le_of_lt (lt_of_not_ge hh)))

theorem radialCutoff_fderiv_zero_outside {r : ℝ} (hr : 0 < r) {y : E} (hy : 2 * r < ‖y‖) :
    fderiv ℝ (radialCutoff (E := E) r) y = 0 := by
  have he : radialCutoff (E := E) r =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [((isOpen_lt continuous_const continuous_norm).mem_nhds hy)] with z hz
    exact radialCutoff_zero hr hz.le
  rw [he.fderiv_eq]
  simp

theorem radialCutoff_fderiv_scale {r : ℝ} (y : E) :
    fderiv ℝ (radialCutoff (E := E) r) y =
      (fderiv ℝ (radialCutoff (E := E) 1) (r⁻¹ • y)).comp (r⁻¹ • ContinuousLinearMap.id ℝ E) := by
  have hlin : HasFDerivAt (fun z : E => r⁻¹ • z) (r⁻¹ • ContinuousLinearMap.id ℝ E) y :=
    (hasFDerivAt_id y).const_smul _
  have h := ((contDiff_radialCutoff (E := E) 1).differentiable (by simp) (r⁻¹ • y)).hasFDerivAt.comp y hlin
  have he : radialCutoff (E := E) r = (radialCutoff (E := E) 1) ∘ (fun z : E => r⁻¹ • z) :=
    funext (radialCutoff_unit_rescale r)
  rw [he]
  exact h.fderiv

theorem radialCutoff_fderiv_bound [FiniteDimensional ℝ E] :
    ∃ C > 0, ∀ (r : ℝ), 0 < r → ∀ y : E, ‖fderiv ℝ (radialCutoff r) y‖ ≤ C / r := by
  obtain ⟨C, hC⟩ := ((hasCompactSupport_radialCutoff (E := E) zero_lt_one).fderiv ℝ).exists_bound_of_continuous
    ((contDiff_radialCutoff 1).continuous_fderiv (by simp))
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro r hr y
  rw [radialCutoff_fderiv_scale]
  calc
    _ ≤ ‖fderiv ℝ (radialCutoff 1) (r⁻¹ • y)‖ * ‖r⁻¹ • ContinuousLinearMap.id ℝ E‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (max C 0 + 1) * (r⁻¹ * 1) := by
      apply mul_le_mul (le_trans (hC _) (by linarith [le_max_left C 0]))
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.mpr hr.le)
      · positivity
      · positivity
    _ = _ := by ring

end OAI.Analysis.PDE.Schauder
