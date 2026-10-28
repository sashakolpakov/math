import OAI.Analysis.PDE.Weak.Elliptic.Difference

/-! Uniform difference-quotient estimates from the actual line integral. -/

noncomputable section
open Set _root_.MeasureTheory
open scoped Topology
namespace OAI.Analysis.PDE.Weak

theorem norm_unit_interval_integral_sq_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (f : ℝ → F) (hf : Continuous f) :
    ‖∫ t in (0 : ℝ)..1, f t‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2 := by
  let ν := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  have hc : ConvexOn ℝ univ (fun y : F ↦ ‖y‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) 2
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hc.map_integral_le (continuous_norm.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ ↦ mem_univ _) (hf.intervalIntegrable 0 1).1
    ((hf.norm.pow 2).intervalIntegrable 0 1).1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_differenceQuotient_sq_le (u : E → F) (hu : ContDiff ℝ 1 u)
    (v x : E) {h : ℝ} (hh : h ≠ 0) :
    ‖differenceQuotient v h u x‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (x + t • (h • v)) v‖ ^ 2 := by
  rw [differenceQuotient_eq_integral u hu v x hh]
  apply norm_unit_interval_integral_sq_le
  exact ((hu.continuous_fderiv one_ne_zero).comp
    (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const

theorem norm_differenceQuotient_le (u : E → F) (hu : ContDiff ℝ 1 u)
    (v x : E) {h M : ℝ} (hh : h ≠ 0)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • (h • v))‖ ≤ M) :
    ‖differenceQuotient v h u x‖ ≤ M * ‖v‖ := by
  rw [differenceQuotient_eq_integral u hu v x hh]
  have hb : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖fderiv ℝ u (x + t • (h • v)) v‖ ≤ M * ‖v‖ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ⟨ht.1.le, ht.2⟩
    exact ((fderiv ℝ u _).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hM t ht') (norm_nonneg v))
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E) [μ.IsAddRightInvariant] [SFinite μ]

omit [SecondCountableTopology E] in
/-- The global L² energy of a difference quotient is bounded by that of the
directional derivative, uniformly for every nonzero step.  No integrability
assumption is needed: this is an extended nonnegative integral inequality. -/
theorem lintegral_differenceQuotient_sq_le (u : E → F) (hu : ContDiff ℝ 1 u)
    (v : E) {h : ℝ} (hh : h ≠ 0) :
    (∫⁻ x, ENNReal.ofReal (‖differenceQuotient v h u x‖ ^ 2) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ u x v‖ ^ 2) ∂μ := by
  let ν := volume.restrict (Ioc (0 : ℝ) 1)
  let H : E → ℝ → ℝ := fun x t ↦ ‖fderiv ℝ u (x + t • (h • v)) v‖ ^ 2
  have hH : Continuous (fun z : E × ℝ ↦ H z.1 z.2) := by
    exact (((hu.continuous_fderiv one_ne_zero).comp
      (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply
      continuous_const).norm.pow 2
  have hpoint (x : E) : ENNReal.ofReal (‖differenceQuotient v h u x‖ ^ 2) ≤
      ∫⁻ t, ENNReal.ofReal (H x t) ∂ν := by
    have hc : Continuous (H x) := hH.comp (continuous_const.prodMk continuous_id)
    have hi : Integrable (H x) ν := (hc.intervalIntegrable (μ := volume) 0 1).1
    have he := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
    rw [← he]
    apply ENNReal.ofReal_le_ofReal
    simpa only [H, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      norm_differenceQuotient_sq_le u hu v x hh
  calc
    _ ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (H x t) ∂ν ∂μ := lintegral_mono hpoint
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (H x t) ∂μ ∂ν :=
      lintegral_lintegral_swap hH.measurable.ennreal_ofReal.aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ u x v‖ ^ 2) ∂μ := by
      have he (t : ℝ) : (∫⁻ x, ENNReal.ofReal (H x t) ∂μ) =
          ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ u x v‖ ^ 2) ∂μ := by
        exact lintegral_add_right_eq_self (fun x ↦ ENNReal.ofReal (‖fderiv ℝ u x v‖ ^ 2))
          (t • (h • v))
      simp only [he, lintegral_const]
      simp [ν]

end OAI.Analysis.PDE.Weak
