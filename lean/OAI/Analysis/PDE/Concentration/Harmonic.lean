import OAI.Analysis.PDE.Concentration.Basic

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem measurable_gaussianDensity : Measurable (fun q : ℝ × ℝ => gaussianDensity q.1 q.2) := by
  unfold gaussianDensity
  fun_prop

theorem gaussianDensity_eq_gaussianPDFReal {s : ℝ} (hs : 0 ≤ s) (T : ℝ) :
    gaussianDensity T s = gaussianPDFReal 0 s.toNNReal T := by
  simp only [gaussianDensity, gaussianPDFReal, Real.coe_toNNReal s hs, sub_zero]
  ring

/-- The real-coordinate exit law obtained by mixing centered Gaussian laws
against the distribution of a positive planar stopping time. -/
noncomputable def gaussianExitMixture (ν : Measure ℝ) : Measure ℝ :=
  volume.withDensity (fun T => ∫⁻ s, ENNReal.ofReal (gaussianDensity T s) ∂ν)

/-- This is the actual Gaussian mixture on every measurable set, not only
a formal density notation. -/
theorem gaussianExitMixture_apply {ν : Measure ℝ} [SFinite ν]
    (hν : ∀ᵐ s ∂ν, 0 < s) {E : Set ℝ} (hE : MeasurableSet E) :
    gaussianExitMixture ν E = ∫⁻ s, gaussianReal 0 s.toNNReal E ∂ν := by
  rw [gaussianExitMixture, withDensity_apply _ hE]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr_ae
    filter_upwards [hν] with s hs
    rw [gaussianReal_apply _ (by exact ne_of_gt (Real.toNNReal_pos.mpr hs))]
    apply lintegral_congr
    intro T
    rw [gaussianDensity_eq_gaussianPDFReal hs.le]
    rfl
  · exact (measurable_gaussianDensity.ennreal_ofReal).aemeasurable

theorem gaussianExitMixture_mass {ν : Measure ℝ} [SFinite ν]
    (hν : ∀ᵐ s ∂ν, 0 < s) : gaussianExitMixture ν Set.univ = ν Set.univ := by
  rw [gaussianExitMixture_apply hν MeasurableSet.univ]
  simp

/-- The full real-time exit measure dominates Lebesgue measure on `[1,2]`
by the same explicit coefficient proved first at the density level. -/
theorem gaussianExitMixture_dominates {ν : Measure ℝ} {L : ℝ}
    (hL : 1 ≤ L) (hν : ∀ᵐ s ∂ν, s ∈ Set.Icc 1 (L ^ 2)) :
    (ENNReal.ofReal (Real.exp (-2) / (Real.sqrt (2 * Real.pi) * L)) * ν Set.univ) •
      volume.restrict (Set.Icc (1 : ℝ) 2) ≤ gaussianExitMixture ν := by
  rw [gaussianExitMixture, ← withDensity_const, ← withDensity_indicator measurableSet_Icc]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro T
  by_cases hT : T ∈ Set.Icc (1 : ℝ) 2
  · rw [Set.indicator_of_mem hT]
    exact gaussian_mixture_lower_bound hT.1 hT.2 hL hν
  · rw [Set.indicator_of_notMem hT]
    exact bot_le

/-- Restricting to a good stopping-time event of mass at least `c/L²`
produces the manuscript's `L⁻³` lower bound as a measure inequality. -/
theorem gaussianExitMixture_dominates_cubic {ν : Measure ℝ} {L c : ℝ}
    (hL : 1 ≤ L)
    (hν : ∀ᵐ s ∂ν, s ∈ Set.Icc 1 (L ^ 2))
    (hmass : ENNReal.ofReal (c / L ^ 2) ≤ ν Set.univ) :
    ENNReal.ofReal ((Real.exp (-2) / Real.sqrt (2 * Real.pi) * c) / L ^ 3) •
      volume.restrict (Set.Icc (1 : ℝ) 2) ≤ gaussianExitMixture ν := by
  apply le_trans ?_ (gaussianExitMixture_dominates hL hν)
  suffices hcoef : ENNReal.ofReal ((Real.exp (-2) / Real.sqrt (2 * Real.pi) * c) / L ^ 3) ≤
      ENNReal.ofReal (Real.exp (-2) / (Real.sqrt (2 * Real.pi) * L)) * ν Set.univ by
    gcongr
  have he : ((Real.exp (-2) / Real.sqrt (2 * Real.pi) * c) / L ^ 3) =
      (Real.exp (-2) / (Real.sqrt (2 * Real.pi) * L)) * (c / L ^ 2) := by
    field_simp
  rw [he, ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul' le_rfl hmass

end OAI.Analysis.PDE.Concentration
