import OAI.Analysis.PDE.Concentration.RegularizedDensity

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current Set
open scoped ContDiff

def packetBaseWave {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : OAI.Analysis.Calculus.Current.Index d → ℝ) : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ :=
  finiteWave (fun i => packetCycleFrequency (κ i) (v i))
    (fun i => OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) x)

theorem smoothedSquare_le_of_sq_le {d : ℕ} {h : ℝ} (hh : 0 < h)
    {f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} {B : ℝ} (hf : ∀ y, ‖f y‖ ^ 2 ≤ B) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    smoothedSquare h f x ≤ B := by
  have hB : 0 ≤ B := (sq_nonneg ‖f 0‖).trans (hf 0)
  have hJ := (OAI.Analysis.Calculus.Current.integrable_smoothingKernel d h hh.ne').comp_sub_left x
  have hb := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => mul_nonneg (OAI.Analysis.Calculus.Current.smoothingKernel_pos d h hh _).le (sq_nonneg ‖f y‖))
    (hJ.mul_const B) (Filter.Eventually.of_forall fun y =>
      mul_le_mul_of_nonneg_left (hf y) (OAI.Analysis.Calculus.Current.smoothingKernel_pos d h hh _).le)
  simpa only [smoothedSquare, integral_mul_const, integral_sub_left_eq_self,
    OAI.Analysis.Calculus.Current.integral_smoothingKernel d h hh, one_mul] using hb

theorem smoothed_gaussian_zero_le_density {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ)
    {h L : ℝ} (hh : 0 < h) (hL : 0 < L) (a : ℝ) (ha : a ≠ 0)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ i, 0 < κ i)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hz : ‖z none‖ = h * L)
    (hcut : ∀ i, radialAngularCutoff ρ χ (Real.sqrt L) (h • packetSpatialFrequency (κ i) (v i)) = 1)
    (hfreq : ∀ i l, ∃ m : ℤ, inner ℝ (packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single l 1)) = (m : ℝ) * (2 * Real.pi) / 100)
    (hr : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a z ≤ 0) (hpatch : ‖OAI.Analysis.Calculus.Current.phi z / (a : ℂ)‖ ≤ 1 / 100)
    (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    smoothedSquare h (packetGaussianField 0 ρ χ h L κ cR cI v x z) y ≤
      OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h a κ cR cI v (x - nullSpatialShift y) z) := by
  have hY : z none ≠ 0 := by
    intro he
    rw [he, norm_zero] at hz
    exact (mul_pos hh hL).ne' hz.symm
  rw [latticeRegularizedCurrent_time_gaussian R ρ χ hh hL a κ cR cI v hκ x z hz hcut hfreq,
    OAI.Analysis.Calculus.Current.phaseCutoff_eq_one _ hpatch, one_mul]
  have h0 := smoothedSquare_nonneg hh (packetGaussianField 1 ρ χ h L κ cR cI v x z) y
  have h1 := mul_nonneg (pow_nonneg hh.le (50 * (d + 1)))
    (OAI.Analysis.Calculus.Current.fiberTimeComponent_pos_on_fiber a z ha hY hr).le
  change 0 ≤ h ^ (50 * (d + 1)) * OAI.Analysis.Calculus.Current.timeComponent (OAI.Analysis.Calculus.Current.fiberCofactor (1 / 10) a z) at h1
  linarith

/-- Recovery lower bound for the actual regularized current throughout an
`h`-ball, with all spatial averaging and lattice quantization proved. -/
theorem packet_density_recovery {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ tsupport ρ, ‖gaussianVelocity η‖ ≤ 1)
    (Rχ RW : ℝ) (hsupp : tsupport χ ⊆ Metric.closedBall 0 Rχ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
      (h L a : ℝ), 0 < h → 1 ≤ L → a ≠ 0 → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ), (∀ i, 0 < κ i) →
      ∀ (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ), ‖z none‖ = h * L →
      ‖transverseRatio z‖ ≤ 1 → Real.sqrt L * ‖transverseRatio z‖ ≤ RW →
      (∀ i, radialAngularCutoff ρ χ (Real.sqrt L) (h • packetSpatialFrequency (κ i) (v i)) = 1) →
      (∀ i l, ∃ m : ℤ, inner ℝ (packetSpatialFrequency (κ i) (v i))
        (R (EuclideanSpace.single l 1)) = (m : ℝ) * (2 * Real.pi) / 100) →
      OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a z ≤ 0 → ‖OAI.Analysis.Calculus.Current.phi z / (a : ℂ)‖ ≤ 1 / 100 →
      ∀ y y' : OAI.Analysis.Calculus.Current.SpatialSpace d, ‖y - y'‖ ≤ h →
      ‖packetBaseWave κ cR cI v x y‖ ^ 2 ≤
        (C * h ^ d * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 + d / 2)) ^ 2 *
          3 ^ (d + 3) * OAI.Analysis.Calculus.Current.timeComponent
            (latticeRegularizedCurrent R h a κ cR cI v (x - nullSpatialShift y') z) := by
  obtain ⟨C, hC, hc⟩ := gaussianWaveOutput_inverse_sq_bound hρ hcρ hχ hcχ hpos hv Rχ RW hsupp
  refine ⟨C, hC, ?_⟩
  intro R h L a hh hL ha ι _ κ cR cI v hκ x z hz hW hRW hcut hfreq hr hpatch y y' hdist
  have hcut' : ∀ i, radialAngularCutoff ρ χ (Real.sqrt L)
      ((2 * Real.pi * h) • packetCycleFrequency (κ i) (v i)) = 1 := by
    intro i
    rw [scaled_packetCycleFrequency]
    exact hcut i
  have hb := hc (transverseRatio z) hW h hh L hL hRW
    (fun i => packetCycleFrequency (κ i) (v i))
    (fun i => OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) x) hcut' y y' hdist
  exact hb.trans (mul_le_mul_of_nonneg_left
    (smoothed_gaussian_zero_le_density R ρ χ hh (by linarith) a ha κ cR cI v hκ x z hz hcut hfreq hr hpatch y')
    (by positivity))

theorem packetGaussianField_smoothed_upper {d : ℕ} (j : Fin 2)
    {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} {χ : TransverseSpace d → ℂ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (w₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h L : ℝ), 0 < h → 1 ≤ L →
      ∀ {ι : Type} [Fintype ι] (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
        (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ), ‖transverseRatio z‖ ≤ w₀ →
      ∀ B : ℝ, (∀ y, ‖packetBaseWave κ cR cI v x y‖ ≤ B) → ∀ y,
      smoothedSquare h (packetGaussianField j ρ χ h L κ cR cI v x z) y ≤
        (C * (h ^ d)⁻¹ * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 - d / 2)) ^ 2 * B ^ 2 := by
  obtain ⟨C, hC, hc⟩ := gaussianWaveOutput_sq_bound j hρ hcρ hχ hcχ hpos w₀
  refine ⟨C, hC, ?_⟩
  intro h L hh hL ι _ κ cR cI v x z hW B hB y
  apply smoothedSquare_le_of_sq_le hh
  intro y'
  have hb := hc (transverseRatio z) hW h hh L hL
    (fun i => packetCycleFrequency (κ i) (v i))
    (fun i => OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) x) y'
  exact hb.trans (mul_le_mul_of_nonneg_left
    (smoothedSquare_le_of_sq_le hh (fun y => pow_le_pow_left₀ (norm_nonneg _) (hB y) 2) y')
    (sq_nonneg _))

/-- The actual input current has the sharp semiclassical supremum bound,
with the source's small cofactor term left explicit for subsequent absorption. -/
theorem packet_density_upper {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (w₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
      (h L a : ℝ), 0 < h → 1 ≤ L → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ), (∀ i, 0 < κ i) →
      ∀ (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ), ‖z none‖ = h * L →
      ‖transverseRatio z‖ ≤ w₀ →
      (∀ i, radialAngularCutoff ρ χ (Real.sqrt L) (h • packetSpatialFrequency (κ i) (v i)) = 1) →
      (∀ i l, ∃ m : ℤ, inner ℝ (packetSpatialFrequency (κ i) (v i))
        (R (EuclideanSpace.single l 1)) = (m : ℝ) * (2 * Real.pi) / 100) →
      ∀ B : ℝ, (∀ y, ‖packetBaseWave κ cR cI v x y‖ ≤ B) → ∀ y,
      OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h a κ cR cI v (x - nullSpatialShift y) z) ≤
        C * ((h ^ d)⁻¹ * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 - d / 2)) ^ 2 * B ^ 2 +
        h ^ (50 * (d + 1)) * OAI.Analysis.Calculus.Current.timeComponent (OAI.Analysis.Calculus.Current.fiberCofactor (1 / 10) a z) := by
  obtain ⟨C₀, hC₀, hc₀⟩ := packetGaussianField_smoothed_upper 0 hρ hcρ hχ hcχ hpos w₀
  obtain ⟨C₁, hC₁, hc₁⟩ := packetGaussianField_smoothed_upper 1 hρ hcρ hχ hcχ hpos w₀
  refine ⟨C₀ ^ 2 + C₁ ^ 2, by positivity, ?_⟩
  intro R h L a hh hL ι _ κ cR cI v hκ x z hz hW hcut hfreq B hB y
  rw [latticeRegularizedCurrent_time_gaussian R ρ χ hh (by linarith) a κ cR cI v hκ x z hz hcut hfreq]
  apply add_le_add _ le_rfl
  have hn := add_nonneg
    (smoothedSquare_nonneg hh (packetGaussianField 0 ρ χ h L κ cR cI v x z) y)
    (smoothedSquare_nonneg hh (packetGaussianField 1 ρ χ h L κ cR cI v x z) y)
  have hp := mul_le_of_le_one_left hn (OAI.Analysis.Calculus.Current.phaseCutoff_le_one (OAI.Analysis.Calculus.Current.phi z / (a : ℂ)))
  apply hp.trans
  have hb := add_le_add (hc₀ h L hh hL κ cR cI v x z hW B hB y)
    (hc₁ h L hh hL κ cR cI v x z hW B hB y)
  convert hb using 1 ; ring

end OAI.Analysis.PDE.Concentration
