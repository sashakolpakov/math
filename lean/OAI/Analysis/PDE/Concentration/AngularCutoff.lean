import OAI.Analysis.PDE.Concentration.GaussianPhase
import OAI.Analysis.PDE.Concentration.ScaledSymbol
import OAI.Analysis.PDE.Concentration.SymbolProduct

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Metric
open scoped ContDiff Topology
open OAI.Analysis.Calculus.Current

def radialAngularCutoff {d : ℕ} (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ)
    (χ : TransverseSpace d → ℂ) (scale : ℝ) (η : OAI.Analysis.Calculus.Current.SpatialSpace d) : ℂ :=
  ρ η * χ (scale • gaussianVelocity η)

theorem radialAngularCutoff_zero_near {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    (χ : TransverseSpace d → ℂ) (scale : ℝ) {η : OAI.Analysis.Calculus.Current.SpatialSpace d}
    (hη : η ∉ tsupport ρ) : radialAngularCutoff ρ χ scale =ᶠ[𝓝 η] 0 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hη] with ξ hξ
  simp [radialAngularCutoff, hξ]

theorem contDiff_radialAngularCutoff {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (scale : ℝ) :
    ContDiff ℝ ∞ (radialAngularCutoff ρ χ scale) := by
  apply contDiff_iff_contDiffAt.mpr
  intro η
  by_cases hη : η ∈ tsupport ρ
  · have hU : IsOpen {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ} :=
      isOpen_lt continuous_const continuous_gaussianFrequencyK
    have hv := (contDiffOn_gaussianVelocity η (hpos η hη)).contDiffAt (hU.mem_nhds (hpos η hη))
    exact hρ.contDiffAt.mul (hχ.contDiffAt.comp η (hv.const_smul scale))
  · exact contDiffAt_const.congr_of_eventuallyEq (radialAngularCutoff_zero_near χ scale hη)

/-- The angular cutoff is constructed from fixed smooth cutoffs and has
the claimed `scale^j` derivative bound, including outside its support. -/
theorem radialAngularCutoff_jets {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ scale : ℝ, 1 ≤ scale → ∀ n ≤ N, ∀ η,
      ‖iteratedFDeriv ℝ n (radialAngularCutoff ρ χ scale) η‖ ≤ C * scale ^ n := by
  have hU : IsOpen {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ} :=
    isOpen_lt continuous_const continuous_gaussianFrequencyK
  obtain ⟨A, hA, ha⟩ := hcρ.exists_bound_iteratedFDeriv hρ N
  obtain ⟨B, hB, hb⟩ := local_scaled_compact_symbol_jets hχ hcχ hcρ hU hpos
    contDiffOn_gaussianVelocity N
  refine ⟨2 ^ N * A * B, by positivity, ?_⟩
  intro scale hs n hn η
  by_cases hη : η ∈ tsupport ρ
  · have hv : ContDiffOn ℝ ∞ (fun ξ => χ (scale • gaussianVelocity ξ))
        {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ} := by
      exact hχ.comp_contDiffOn (contDiffOn_gaussianVelocity.const_smul scale)
    have hh := local_scaled_product_jets hU hρ.contDiffOn hv hA hB (by linarith)
      (hpos η hη) n
      (fun j hj => (ha j (hj.trans hn) η).trans
        (le_mul_of_one_le_right hA (one_le_pow₀ hs)))
      (fun j hj => hb η hη scale hs j (hj.trans hn))
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn) hA) hB)
      (pow_nonneg (by linarith) n))
  · have he := (radialAngularCutoff_zero_near χ scale hη).iteratedFDeriv ℝ n
    rw [he.self_of_nhds]
    simp only [Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
    positivity

/-- Outside the angular patch the cutoff vanishes on a neighborhood,
so every derivative vanishes there as well. -/
theorem radialAngularCutoff_zero_near_large_velocity {d : ℕ}
    (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) {χ : TransverseSpace d → ℂ} {R scale : ℝ}
    (hχ : tsupport χ ⊆ closedBall 0 R) {η : OAI.Analysis.Calculus.Current.SpatialSpace d}
    (hη : 0 < gaussianFrequencyK η) (hlarge : R < ‖scale • gaussianVelocity η‖) :
    radialAngularCutoff ρ χ scale =ᶠ[𝓝 η] 0 := by
  have hU : IsOpen {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ} :=
    isOpen_lt continuous_const continuous_gaussianFrequencyK
  have hv := ((contDiffOn_gaussianVelocity η hη).contDiffAt (hU.mem_nhds hη)).continuousAt
  have hh : ∀ᶠ ξ in 𝓝 η, R < ‖scale • gaussianVelocity ξ‖ :=
    (hv.const_smul scale).norm.eventually (Ioi_mem_nhds hlarge)
  filter_upwards [hh] with ξ hξ
  have hz : χ (scale • gaussianVelocity ξ) = 0 := by
    by_contra hn
    have hm := hχ (subset_closure (show scale • gaussianVelocity ξ ∈ Function.support χ from hn))
    have hm' : ‖scale • gaussianVelocity ξ‖ ≤ R := by simpa using hm
    exact (not_le.mpr hξ) hm'
  simp [radialAngularCutoff, hz]

end OAI.Analysis.PDE.Concentration
