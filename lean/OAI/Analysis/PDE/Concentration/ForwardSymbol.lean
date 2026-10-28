import OAI.Analysis.PDE.Concentration.AngularCutoff
import OAI.Analysis.PDE.Concentration.GaussianPrefactor

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Metric
open scoped ContDiff Topology
open OAI.Analysis.Calculus.Current

def gaussianForwardCore {d : ℕ} (j : Fin 2) (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ)
    (χ : TransverseSpace d → ℂ) (L : ℝ) (W : TransverseSpace d) (η : OAI.Analysis.Calculus.Current.SpatialSpace d) : ℂ :=
  radialAngularCutoff ρ χ (Real.sqrt L) η *
    (gaussianForwardAmplitude j (W, η) * Complex.exp
      (-(L / 2 * gaussianFrequencyK η * ‖W - gaussianVelocity η‖ ^ 2 : ℝ)))

theorem gaussianForwardCore_zero_near {d : ℕ} (j : Fin 2) {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    (χ : TransverseSpace d → ℂ) (L : ℝ) (W : TransverseSpace d) {η : OAI.Analysis.Calculus.Current.SpatialSpace d}
    (hη : η ∉ tsupport ρ) : gaussianForwardCore j ρ χ L W =ᶠ[𝓝 η] 0 := by
  filter_upwards [radialAngularCutoff_zero_near χ (Real.sqrt L) hη] with ξ hξ
  simp [gaussianForwardCore, hξ]

theorem contDiff_gaussianForwardCore {d : ℕ} (j : Fin 2) {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) {L : ℝ} (hL : 0 ≤ L)
    (W : TransverseSpace d) : ContDiff ℝ ∞ (gaussianForwardCore j ρ χ L W) := by
  have hU : IsOpen {η : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK η} :=
    isOpen_lt continuous_const continuous_gaussianFrequencyK
  have ha : ContDiffOn ℝ ∞ (fun η => gaussianForwardAmplitude j (W, η))
      {η : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK η} :=
    (contDiffOn_gaussianForwardAmplitude j).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  apply contDiff_iff_contDiffAt.mpr
  intro η
  by_cases hη : η ∈ tsupport ρ
  · exact (contDiff_radialAngularCutoff hρ hχ hpos _).contDiffAt.mul
      ((ha.mul (contDiffOn_sourceGaussian W hL) η (hpos η hη)).contDiffAt (hU.mem_nhds (hpos η hη)))
  · exact contDiffAt_const.congr_of_eventuallyEq (gaussianForwardCore_zero_near j χ L W hη)

/-- Full forward symbol before the scalar `h⁻ᵈ L⁻ᵈ/²` normalization.
Every derivative bound, including the cutoff's, is derived from fixed smooth data. -/
theorem gaussianForwardCore_jets {d : ℕ} (j : Fin 2) {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (w₀ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ w₀ →
      ∀ L : ℝ, 1 ≤ L → ∀ n ≤ N, ∀ η,
      ‖iteratedFDeriv ℝ n (gaussianForwardCore j ρ χ L W) η‖ ≤ C * L ^ ((n : ℝ) / 2) := by
  have hU : IsOpen {p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK p.2} :=
    isOpen_lt continuous_const (continuous_gaussianFrequencyK.comp continuous_snd)
  have hV : IsOpen {η : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK η} :=
    isOpen_lt continuous_const continuous_gaussianFrequencyK
  obtain ⟨A, hA, ha⟩ := compact_local_family_spatial_jets
    (isCompact_closedBall (0 : TransverseSpace d) w₀) hcρ hU
    (fun p hp => hpos p.2 hp.2) (contDiffOn_gaussianForwardAmplitude j) N
  obtain ⟨B, hB, hb⟩ := uniform_gaussian_phase_jets hcρ hpos w₀ N
  obtain ⟨D, hD, hd⟩ := radialAngularCutoff_jets hρ hcρ hχ hcχ hpos N
  let E := 2 ^ N * A * B
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨2 ^ N * D * E, by positivity, ?_⟩
  intro W hW L hL n hn η
  have hs : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
  have hL0 : 0 ≤ L := by linarith
  by_cases hη : η ∈ tsupport ρ
  · have ha' : ContDiffOn ℝ ∞ (fun ξ => gaussianForwardAmplitude j (W, ξ))
        {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ} :=
      (contDiffOn_gaussianForwardAmplitude j).comp
        (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
    let f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ := fun ξ => gaussianForwardAmplitude j (W, ξ) * Complex.exp
      (-(L / 2 * gaussianFrequencyK ξ * ‖W - gaussianVelocity ξ‖ ^ 2 : ℝ))
    have hf : ContDiffOn ℝ ∞ f {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ} :=
      ha'.mul (contDiffOn_sourceGaussian W hL0)
    have hfb : ∀ q ≤ n, ‖iteratedFDeriv ℝ q f η‖ ≤ E * Real.sqrt L ^ q := by
      intro q hq
      have hbg : ∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun ξ : OAI.Analysis.Calculus.Current.SpatialSpace d => Complex.exp
          (-(L / 2 * gaussianFrequencyK ξ * ‖W - gaussianVelocity ξ‖ ^ 2 : ℝ))) η‖ ≤
          B * Real.sqrt L ^ i := by
        intro i hi
        rw [sqrt_pow_eq_half_rpow hL0]
        exact hb W hW η hη L hL i ((hi.trans hq).trans hn)
      have hh := local_scaled_product_jets hV ha' (contDiffOn_sourceGaussian W hL0)
        hA hB (Real.sqrt_nonneg L) (hpos η hη) q
        (fun i hi => (ha W (by simpa using hW) η hη i ((hi.trans hq).trans hn)).trans
          (le_mul_of_one_le_right hA (one_le_pow₀ hs)))
        hbg
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hq.trans hn)) hA) hB)
        (pow_nonneg (Real.sqrt_nonneg L) q))
    have hh := local_scaled_product_jets hV
      (contDiff_radialAngularCutoff hρ hχ hpos _).contDiffOn hf hD hE (Real.sqrt_nonneg L)
      (hpos η hη) n (fun i hi => hd _ hs i (hi.trans hn) η) hfb
    have hh' := hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn) hD) hE)
      (pow_nonneg (Real.sqrt_nonneg L) n))
    have he : (fun ξ => radialAngularCutoff ρ χ (Real.sqrt L) ξ * f ξ) =
        gaussianForwardCore j ρ χ L W := by
      funext ξ
      rfl
    rw [he, sqrt_pow_eq_half_rpow hL0] at hh'
    exact hh'
  · rw [((gaussianForwardCore_zero_near j χ L W hη).iteratedFDeriv ℝ n).self_of_nhds]
    simp only [Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
    positivity

def gaussianForwardSymbol {d : ℕ} (j : Fin 2) (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ)
    (χ : TransverseSpace d → ℂ) (h L : ℝ) (W : TransverseSpace d) : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ :=
  ((h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2)) • gaussianForwardCore j ρ χ L W

/-- The normalized forward symbols satisfy the exact input derivative
exponents `h⁻ᵈ L^((j-d)/2)` from the manuscript. -/
theorem gaussianForwardSymbol_jets {d : ℕ} (j : Fin 2) {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (w₀ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ w₀ →
      ∀ h : ℝ, 0 < h → ∀ L : ℝ, 1 ≤ L → ∀ n ≤ N, ∀ η,
      ‖iteratedFDeriv ℝ n (gaussianForwardSymbol j ρ χ h L W) η‖ ≤
        C * (h ^ d)⁻¹ * L ^ (((n : ℝ) - d) / 2) := by
  obtain ⟨C, hC, hc⟩ := gaussianForwardCore_jets j hρ hcρ hχ hcχ hpos w₀ N
  refine ⟨C, hC, ?_⟩
  intro W hW h hh L hL n hn η
  have hL0 : 0 ≤ L := by linarith
  have hfac : 0 ≤ (h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2) := by positivity
  have he : L ^ (-(d : ℝ) / 2) * L ^ ((n : ℝ) / 2) =
      L ^ (((n : ℝ) - d) / 2) := by
    rw [← Real.rpow_add (by linarith : 0 < L)]
    congr 1
    ring
  unfold gaussianForwardSymbol
  rw [iteratedFDeriv_const_smul_apply
    ((contDiff_gaussianForwardCore j hρ hχ hpos hL0 W).of_le (by simp)).contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac]
  calc
    _ ≤ ((h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2)) * (C * L ^ ((n : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (hc W hW L hL n hn η) hfac
    _ = C * (h ^ d)⁻¹ * L ^ (((n : ℝ) - d) / 2) := by
      rw [show ((h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2)) * (C * L ^ ((n : ℝ) / 2)) =
        C * (h ^ d)⁻¹ * (L ^ (-(d : ℝ) / 2) * L ^ ((n : ℝ) / 2)) by ring, he]

end OAI.Analysis.PDE.Concentration
