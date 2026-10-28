import OAI.RepresentationTheory.Weil.Local.FresnelLimit

/-! # Fourier Pairing Limit -/

namespace OAI.RepresentationTheory.Weil.Local.FourierPairingLimit.Construction

noncomputable section

/-! A dominated-convergence criterion for Fourier pairing against bounded limiting kernels. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem fourier_pairing_of_dominated_cutoffs
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [SigmaFinite μ]
    (g : ℝ → FunctionsMetaplectic.Construction.Position k n → ℂ) (q r : FunctionsMetaplectic.Construction.Position k n → ℂ) (a : ℂ) (B : ℝ)
    (hgi : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Integrable (g ε) μ)
    (hgb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, ‖g ε x‖ ≤ 1)
    (hgl : ∀ x, Tendsto (fun ε => g ε x) (𝓝[>] (0 : ℝ)) (𝓝 (q x)))
    (hFb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, ‖FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g ε) x‖ ≤ B)
    (hFl : ∀ x, Tendsto (fun ε => FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g ε) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (a * r x)))
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : Integrable f μ) (hF : Integrable (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) μ) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x * q x ∂μ) =
      a * ∫ x, f x * r x ∂μ := by
  have hleft : Tendsto (fun ε : ℝ => ∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x * g ε x ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x * q x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x‖)
    · filter_upwards [hgi] with ε hε
      exact hF.aestronglyMeasurable.mul hε.aestronglyMeasurable
    · filter_upwards [hgb] with ε hε
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hε x)
    · exact hF.norm
    · exact Eventually.of_forall fun x => (hgl x).const_mul _
  have hright : Tendsto (fun ε : ℝ => ∫ x, f x * FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g ε) x ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x * (a * r x) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖ * B)
    · filter_upwards [hgi] with ε hε
      exact hf.aestronglyMeasurable.mul (FourierTools.Construction.fourierIntegral_continuous ψ hu hc μ hε).aestronglyMeasurable
    · filter_upwards [hFb] with ε hε
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hε x) (norm_nonneg _)
    · exact hf.norm.mul_const B
    · exact Eventually.of_forall fun x => (hFl x).const_mul _
  have heq := hleft.congr' (show (fun ε : ℝ => ∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x * g ε x ∂μ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => ∫ x, f x * FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g ε) x ∂μ) from by
    filter_upwards [hgi] with ε hε
    exact FresnelLimit.Construction.fourierIntegral_mul_swap ψ hu hc μ hf hε)
  rw [tendsto_nhds_unique heq hright, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

end

end OAI.RepresentationTheory.Weil.Local.FourierPairingLimit.Construction
