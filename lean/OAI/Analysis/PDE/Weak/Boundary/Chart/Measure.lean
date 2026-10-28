import OAI.Analysis.PDE.Weak.Boundary.Weak.Pullback

/-! The bounded distortion estimate required to pull L² and Sobolev
functions through a boundary-flattening chart. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem chart_map_measure_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {U V : Set E} (_ : MeasurableSet U) (hV : MeasurableSet V)
    {G P : E → E} (hG : Measurable G) (hP : DifferentiableOn ℝ P V)
    (hGU : MapsTo G U V) (hPV : MapsTo P V U)
    (hPG : ∀ x ∈ U, P (G x) = x) (hGP : ∀ x ∈ V, G (P x) = x)
    {C : ℝ} (hC : ∀ x ∈ V, |(fderivWithin ℝ P V x).det| ≤ C) :
    Measure.map G (μ.restrict U) ≤ ENNReal.ofReal C • μ := by
  apply Measure.le_iff.mpr
  intro s hs
  have hinj : InjOn P V := by
    intro x hx y hy he
    have hh := congrArg G he
    simpa only [hGP x hx, hGP y hy] using hh
  have himage : P '' (s ∩ V) = G ⁻¹' s ∩ U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by simpa only [mem_preimage, hGP y hy.2] using hy.1, hPV hy.2⟩
    · rintro ⟨hx, hxU⟩
      exact ⟨G x, ⟨hx, hGU hxU⟩, hPG x hxU⟩
  have hderiv : ∀ x ∈ s ∩ V, HasFDerivWithinAt P (fderivWithin ℝ P V x) (s ∩ V) x := by
    intro x hx
    exact (hP x hx.2).hasFDerivWithinAt.mono inter_subset_right
  rw [Measure.map_apply hG hs, Measure.restrict_apply (hs.preimage hG),
    ← himage, ← lintegral_abs_det_fderiv_eq_addHaar_image μ (hs.inter hV) hderiv
      (hinj.mono inter_subset_right), Measure.smul_apply, smul_eq_mul]
  calc
    (∫⁻ x in s ∩ V, ENNReal.ofReal |(fderivWithin ℝ P V x).det| ∂μ) ≤
        ∫⁻ _x in s ∩ V, ENNReal.ofReal C ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hs.inter hV)] with x hx
      exact ENNReal.ofReal_le_ofReal (hC x hx.2)
    _ = ENNReal.ofReal C * μ (s ∩ V) := by simp
    _ ≤ ENNReal.ofReal C * μ s := mul_le_mul_of_nonneg_left (measure_mono inter_subset_left) (by positivity)

theorem chart_map_measure_le_of_fderiv (μ : Measure E) [μ.IsAddHaarMeasure]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {G P : E → E} (hG : Continuous G) (hP : Differentiable ℝ P)
    (hGU : MapsTo G U V) (hPV : MapsTo P V U)
    (hPG : ∀ x ∈ U, P (G x) = x) (hGP : ∀ x ∈ V, G (P x) = x)
    {C : ℝ} (hC : ∀ x ∈ V, |(fderiv ℝ P x).det| ≤ C) :
    Measure.map G (μ.restrict U) ≤ ENNReal.ofReal C • μ := by
  apply chart_map_measure_le μ hU.measurableSet hV.measurableSet hG.measurable
    hP.differentiableOn hGU hPV hPG hGP
  intro x hx
  rw [fderivWithin_of_isOpen hV hx]
  exact hC x hx

end OAI.Analysis.PDE.Weak
