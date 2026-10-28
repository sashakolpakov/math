import OAI.Analysis.PDE.Concentration.Packet.L2
import OAI.Analysis.PDE.Concentration.SmoothingMass

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current
open scoped ContDiff

theorem integral_smoothed_packetGaussianField {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (j : Fin 2)
    (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ)
    {h : ℝ} (hh : 0 < h) (L : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hinj : Function.Injective m)
    (hm : ∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k)) (R (EuclideanSpace.single i 1)) =
      (m k i : ℝ) * (2 * Real.pi) / 100) (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) :
    (∫ y in physicalSpatialCell R, smoothedSquare h (packetGaussianField j ρ χ h L κ cR cI v x z) y) =
      ∫ y in physicalSpatialCell R, ‖packetGaussianField j ρ χ h L κ cR cI v x z y‖ ^ 2 :=
  integral_smoothed_finiteWave R _ m hinj _
    (fun k => packetCycleFrequency_basis R (κ k) (v k) (m k) (hm k)) hh

/-- Integrated input density on the physical spatial cell. The logarithmic
factor is `L⁻ᵈ`, rather than the larger pointwise derivative loss. -/
theorem packet_spatial_density_upper {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (w₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
      (h L a : ℝ), 0 < h → 1 ≤ L → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ),
      Function.Injective m → (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k)) (R (EuclideanSpace.single i 1)) =
        (m k i : ℝ) * (2 * Real.pi) / 100) →
      ∀ (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ), ‖z none‖ = h * L → ‖transverseRatio z‖ ≤ w₀ →
      (∀ i, radialAngularCutoff ρ χ (Real.sqrt L) (h • packetSpatialFrequency (κ i) (v i)) = 1) →
      (∫ y in physicalSpatialCell R,
        OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h a κ cR cI v (x - nullSpatialShift y) z)) ≤
        C * ((h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2)) ^ 2 *
          (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v x y‖ ^ 2) +
        volume.real (physicalSpatialCell R) *
          (h ^ (50 * (d + 1)) * OAI.Analysis.Calculus.Current.timeComponent (OAI.Analysis.Calculus.Current.fiberCofactor (1 / 10) a z)) := by
  obtain ⟨C₀, hC₀, hc₀⟩ := packetGaussianField_L2 0 hρ hcρ hχ hcχ hpos w₀
  obtain ⟨C₁, hC₁, hc₁⟩ := packetGaussianField_L2 1 hρ hcρ hχ hcχ hpos w₀
  refine ⟨C₀ ^ 2 + C₁ ^ 2, by positivity, ?_⟩
  intro R h L a hh hL ι _ κ cR cI v m hinj hκ hm x z hz hW hcut
  let : IsFiniteMeasure (volume.restrict (physicalSpatialCell R)) :=
    isFiniteMeasure_restrict.mpr (physicalSpatialCell_finite R)
  have hi (j : Fin 2) : IntegrableOn
      (smoothedSquare h (packetGaussianField j ρ χ h L κ cR cI v x z)) (physicalSpatialCell R) :=
    integrableOn_smoothedSquare hh _ (continuous_packetGaussianField j ρ χ h L κ cR cI v x z)
      (norm_finiteWave_le _ _) (physicalSpatialCell_finite R)
  have he := fun y => latticeRegularizedCurrent_time_gaussian R ρ χ hh
    (show 0 < L by linarith) a κ cR cI v hκ x z hz hcut (fun k i => ⟨m k i, hm k i⟩) y
  simp_rw [he]
  have hsplit := integral_add (((hi 0).add (hi 1)).const_mul (OAI.Analysis.Calculus.Current.phaseCutoff (OAI.Analysis.Calculus.Current.phi z / (a : ℂ))))
    (integrable_const (h ^ (50 * (d + 1)) * OAI.Analysis.Calculus.Current.timeComponent (OAI.Analysis.Calculus.Current.fiberCofactor (1 / 10) a z)))
  have hsum := integral_add (hi 0) (hi 1)
  simp only [Pi.add_apply] at hsplit hsum
  rw [hsplit, integral_const_mul, hsum, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  rw [integral_smoothed_packetGaussianField R 0 ρ χ hh L κ cR cI v m hinj hm x z,
    integral_smoothed_packetGaussianField R 1 ρ χ hh L κ cR cI v m hinj hm x z]
  apply add_le_add _ le_rfl
  have hn : 0 ≤ (∫ y in physicalSpatialCell R, ‖packetGaussianField 0 ρ χ h L κ cR cI v x z y‖ ^ 2) +
      ∫ y in physicalSpatialCell R, ‖packetGaussianField 1 ρ χ h L κ cR cI v x z y‖ ^ 2 :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  apply (mul_le_of_le_one_left hn (OAI.Analysis.Calculus.Current.phaseCutoff_le_one _)).trans
  have hb := add_le_add (hc₀ R h L hh hL κ cR cI v m hinj hm x z hW)
    (hc₁ R h L hh hL κ cR cI v m hinj hm x z hW)
  convert hb using 1 ; ring

end OAI.Analysis.PDE.Concentration
