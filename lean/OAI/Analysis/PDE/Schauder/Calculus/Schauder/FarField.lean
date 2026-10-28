import OAI.Analysis.PDE.Schauder.Calculus.Schauder.KernelVariation
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.TailIntegral

/-! The far-field part of the Newtonian singular-integral Hölder estimate. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def newtonianFarEntry (f : E → ℝ) (x h v w y : E) : ℝ :=
  (newtonianEntry (Module.finrank ℝ E) v w (y - h) -
    newtonianEntry (Module.finrank ℝ E) v w y) * (f (x - y) - f x)

omit [FiniteDimensional ℝ E] in
theorem measurable_newtonianEntry (m : ℕ) (v w : E) :
    Measurable (newtonianEntry m v w) :=
  (ContinuousLinearMap.measurable_apply w).comp
    ((ContinuousLinearMap.measurable_apply v).comp (measurable_newtonianSecond m))

theorem measurable_newtonianFarEntry (f : E → ℝ) (hf : Measurable f) (x h v w : E) :
    Measurable (newtonianFarEntry f x h v w) := by
  exact (((measurable_newtonianEntry _ v w).comp
    (measurable_id.sub measurable_const)).sub (measurable_newtonianEntry _ v w)).mul
    ((hf.comp (measurable_const.sub measurable_id)).sub measurable_const)

omit [MeasurableSpace E] [BorelSpace E] in
theorem newtonian_far_difference_constant (m : ℕ) (v w : E) :
    ∃ C > 0, ∀ y h : E, y ≠ 0 → 2 * ‖h‖ ≤ ‖y‖ →
      |newtonianEntry m v w (y - h) - newtonianEntry m v w y| ≤
        C * ‖h‖ * ‖y‖ ^ (-(m : ℝ) - 1) := by
  obtain ⟨C, hC, hbound⟩ := newtonianEntry_difference_bound (E := E) m v w
  refine ⟨C * (2⁻¹ : ℝ) ^ (-(m : ℝ) - 1), by positivity, ?_⟩
  intro y h hy hh
  have he : ‖y - h - y‖ = ‖h‖ := by rw [sub_right_comm, sub_self, zero_sub, norm_neg]
  have hb := hbound y (y - h) hy (by rw [he]; linarith)
  rw [he, div_eq_mul_inv, Real.mul_rpow (norm_nonneg y) (by positivity)] at hb
  convert hb using 1 ; ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem newtonianFarEntry_bound (f : E → ℝ) (x h v w y : E) {H α C : ℝ}
    (_ : 0 ≤ H) (hC : 0 ≤ C)
    (hholder : |f (x - y) - f x| ≤ H * ‖y‖ ^ α)
    (hkernel : |newtonianEntry (Module.finrank ℝ E) v w (y - h) -
      newtonianEntry (Module.finrank ℝ E) v w y| ≤
        C * ‖h‖ * ‖y‖ ^ (-(Module.finrank ℝ E : ℝ) - 1))
    (hy : y ≠ 0) :
    ‖newtonianFarEntry f x h v w y‖ ≤
      C * H * ‖h‖ * ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ) - 1) := by
  rw [newtonianFarEntry, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (C * ‖h‖ * ‖y‖ ^ (-(Module.finrank ℝ E : ℝ) - 1)) * (H * ‖y‖ ^ α) :=
      mul_le_mul hkernel hholder (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [show α - (Module.finrank ℝ E : ℝ) - 1 =
        (-(Module.finrank ℝ E : ℝ) - 1) + α by ring,
        Real.rpow_add (norm_pos_iff.mpr hy)]
      ring

theorem newtonian_farField_estimate (v w : E) :
    ∃ C > 0, ∀ (f : E → ℝ) (x h : E) (H α R : ℝ) (μ : Measure E),
      μ.IsAddHaarMeasure → 1 ≤ Module.finrank ℝ E → Measurable f →
      0 ≤ H → α < 1 → 0 < R → 2 * ‖h‖ ≤ R →
      (∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α) →
      IntegrableOn (newtonianFarEntry f x h v w) {y : E | R < ‖y‖} μ ∧
      |∫ y in {y : E | R < ‖y‖}, newtonianFarEntry f x h v w y ∂μ| ≤
        C * H * ‖h‖ * R ^ (α - 1) * rieszTailMass μ α := by
  obtain ⟨C, hC, hb⟩ := newtonian_far_difference_constant (Module.finrank ℝ E) v w
  refine ⟨C, hC, ?_⟩
  intro f x h H α R μ hμ hd hf hH hα hR hh hholder
  let := hμ
  have hmajor := (integrableOn_riesz_tail μ hd hα hR).const_mul (C * H * ‖h‖)
  have hbound : ∀ᵐ y ∂μ.restrict {y : E | R < ‖y‖},
      ‖newtonianFarEntry f x h v w y‖ ≤
        C * H * ‖h‖ * ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ) - 1) := by
    filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const continuous_norm.measurable)] with y hy
    have hy0 : y ≠ 0 := norm_pos_iff.mp (hR.trans hy)
    exact newtonianFarEntry_bound f x h v w y hH hC.le (hholder y)
      (hb y h hy0 (hh.trans hy.le)) hy0
  refine ⟨hmajor.mono' (measurable_newtonianFarEntry f hf x h v w).aestronglyMeasurable hbound, ?_⟩
  have hi := norm_integral_le_of_norm_le hmajor hbound
  rw [integral_const_mul, integral_riesz_tail μ α hR] at hi
  simpa only [Real.norm_eq_abs, mul_assoc] using hi

theorem newtonian_farField_holder (v w : E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hd : 1 ≤ Module.finrank ℝ E) {α : ℝ} (hα : α < 1) :
    ∃ C > 0, ∀ (f : E → ℝ) (x h : E) (H : ℝ), Measurable f → 0 ≤ H → h ≠ 0 →
      (∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α) →
      |∫ y in {y : E | 2 * ‖h‖ < ‖y‖}, newtonianFarEntry f x h v w y ∂μ| ≤
        C * H * ‖h‖ ^ α := by
  obtain ⟨C, hC, hb⟩ := newtonian_farField_estimate v w
  refine ⟨C * 2 ^ (α - 1) * (rieszTailMass μ α + 1), by
    have := rieszTailMass_nonneg μ α
    positivity, ?_⟩
  intro f x h H hf hH hh hholder
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hi := (hb f x h H α (2 * ‖h‖) μ inferInstance hd hf hH hα (by positivity)
    le_rfl hholder).2
  have he : ‖h‖ * (2 * ‖h‖) ^ (α - 1) = 2 ^ (α - 1) * ‖h‖ ^ α := by
    rw [Real.mul_rpow (by norm_num) hn.le]
    have ht : ‖h‖ * ‖h‖ ^ (α - 1) = ‖h‖ ^ α := by
      rw [mul_comm, ← Real.rpow_add_one hn.ne', sub_add_cancel]
    calc
      _ = 2 ^ (α - 1) * (‖h‖ * ‖h‖ ^ (α - 1)) := by ring
      _ = _ := by rw [ht]
  calc
    _ ≤ C * H * ‖h‖ * (2 * ‖h‖) ^ (α - 1) * rieszTailMass μ α := hi
    _ = (C * 2 ^ (α - 1) * rieszTailMass μ α) * H * ‖h‖ ^ α := by
      calc
        _ = C * H * (‖h‖ * (2 * ‖h‖) ^ (α - 1)) * rieszTailMass μ α := by ring
        _ = _ := by rw [he]; ring
    _ ≤ _ := by
      have hr : 0 ≤ (2 : ℝ) ^ (α - 1) := Real.rpow_nonneg (by norm_num) _
      have hhα : 0 ≤ ‖h‖ ^ α := Real.rpow_nonneg hn.le _
      nlinarith [mul_nonneg (mul_nonneg hC.le hr) (mul_nonneg hH hhα)]

end OAI.Analysis.PDE.Schauder
