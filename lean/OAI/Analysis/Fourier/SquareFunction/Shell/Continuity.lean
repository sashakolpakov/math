import OAI.Analysis.Fourier.BochnerRiesz.Shell.Formula

open OAI.Analysis.Fourier.Wave

/-! Joint continuity in physical space and the shell radius. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform

theorem continuous_thinShellCycles_joint {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    Continuous (fun z : Space n × ℝ => thinShellCycles φ δ f z.1 z.2) := by
  let B := SchwartzMap.seminorm ℝ 0 0 φ
  let G := fun (z : Space n × ℝ) (ξ : Space n) =>
    φ ((z.2 - ‖ξ‖) / δ) * (spatialPhase z.1 ξ * (𝓕 f) ξ)
  have he : (fun z : Space n × ℝ => thinShellCycles φ δ f z.1 z.2) =
      (fun z => ∫ ξ, G z ξ) := by
    funext z
    exact congrFun (thinShellCycles_eq_radiusSuperposition φ δ f z.1) z.2
  rw [he]
  have hm (z : Space n × ℝ) : AEStronglyMeasurable (G z) volume :=
    ((φ.continuous.measurable.comp
      ((measurable_const.sub continuous_norm.measurable).div_const δ)).mul
        ((continuous_spatialPhase z.1).measurable.mul (𝓕 f).continuous.measurable)).aestronglyMeasurable
  have hb (z : Space n × ℝ) (ξ : Space n) : ‖G z ξ‖ ≤ B * ‖(𝓕 f) ξ‖ := by
    simp only [G, norm_mul, norm_spatialPhase, one_mul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ φ _) (norm_nonneg _)
  have hcont (ξ : Space n) : Continuous (fun z : Space n × ℝ => G z ξ) := by
    dsimp only [G, spatialPhase]
    have hφ := φ.continuous
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_integral_filter_of_dominated_convergence (fun ξ => B * ‖(𝓕 f) ξ‖)
  · exact Filter.Eventually.of_forall hm
  · exact Filter.Eventually.of_forall fun z => Filter.Eventually.of_forall (hb z)
  · exact (𝓕 f).integrable.norm.const_mul B
  · exact Filter.Eventually.of_forall fun ξ => (hcont ξ).tendsto z

theorem continuous_thinShellCycles_radius {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : Continuous (thinShellCycles φ δ f x) := by
  rw [thinShellCycles_eq_radiusSuperposition]
  exact OAI.Analysis.Fourier.BochnerRiesz.continuous_radiusSuperposition volume φ δ continuous_norm.measurable
    (integrable_spatialPhase_mul x (𝓕 f).integrable)

end OAI.Analysis.Fourier.SquareFunction
