import OAI.Analysis.PDE.Concentration.ForwardSymbol

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Metric
open scoped ContDiff Topology
open OAI.Analysis.Calculus.Current

theorem isOpen_gaussianPositiveRegion {d : ℕ} :
    IsOpen {p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK p.2 ∧ 0 < gaussianB0 p} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hk : {q : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK q.2} ∈ 𝓝 p :=
    (isOpen_lt continuous_const (continuous_gaussianFrequencyK.comp continuous_snd)).mem_nhds hp.1
  have hb : {q : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianB0 q} ∈ 𝓝 p :=
    (contDiffAt_gaussianB0 hp.1).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hp.2)
  exact inter_mem hk hb

def gaussianInverseCore {d : ℕ} (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ)
    (χ : TransverseSpace d → ℂ) (L : ℝ) (W : TransverseSpace d) (η : OAI.Analysis.Calculus.Current.SpatialSpace d) : ℂ :=
  radialAngularCutoff ρ χ (Real.sqrt L) η *
    (gaussianInverseAmplitude (W, η) * Complex.exp
      ((L / 2 * gaussianFrequencyK η * ‖W - gaussianVelocity η‖ ^ 2 : ℝ)))

theorem gaussianInverseCore_zero_near {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    (χ : TransverseSpace d → ℂ) (L : ℝ) (W : TransverseSpace d) {η : OAI.Analysis.Calculus.Current.SpatialSpace d}
    (hη : η ∉ tsupport ρ) : gaussianInverseCore ρ χ L W =ᶠ[𝓝 η] 0 := by
  filter_upwards [radialAngularCutoff_zero_near χ (Real.sqrt L) hη] with ξ hξ
  simp [gaussianInverseCore, hξ]

theorem contDiff_gaussianInverseCore {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ tsupport ρ, ‖gaussianVelocity η‖ ≤ 1) {L : ℝ} (hL : 0 ≤ L)
    (W : TransverseSpace d) (hW : ‖W‖ ≤ 1) : ContDiff ℝ ∞ (gaussianInverseCore ρ χ L W) := by
  have hV : IsOpen {η : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK η ∧ 0 < gaussianB0 (W, η)} :=
    isOpen_gaussianPositiveRegion.preimage (continuous_const.prodMk continuous_id)
  have ha : ContDiffOn ℝ ∞ (fun η => gaussianInverseAmplitude (W, η))
      {η : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK η ∧ 0 < gaussianB0 (W, η)} :=
    contDiffOn_gaussianInverseAmplitude.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  apply contDiff_iff_contDiffAt.mpr
  intro η
  by_cases hη : η ∈ tsupport ρ
  · have hh : 0 < gaussianFrequencyK η ∧ 0 < gaussianB0 (W, η) :=
      ⟨hpos η hη, gaussianB0_pos_of_small hW (hv η hη)⟩
    exact (contDiff_radialAngularCutoff hρ hχ hpos _).contDiffAt.mul
      ((ha.mul ((contDiffOn_sourceInverseGaussian W hL).mono (fun _ h => h.1)) η hh).contDiffAt
        (hV.mem_nhds hh))
  · exact contDiffAt_const.congr_of_eventuallyEq (gaussianInverseCore_zero_near χ L W hη)

/-- The actual reciprocal symbol is controlled globally, because the cutoff
vanishes to all orders off its angular patch. -/
theorem gaussianInverseCore_jets {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ tsupport ρ, ‖gaussianVelocity η‖ ≤ 1)
    (Rχ RW : ℝ) (hsupp : tsupport χ ⊆ closedBall 0 Rχ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ 1 →
      ∀ L : ℝ, 1 ≤ L → Real.sqrt L * ‖W‖ ≤ RW → ∀ n ≤ N, ∀ η,
      ‖iteratedFDeriv ℝ n (gaussianInverseCore ρ χ L W) η‖ ≤ C * L ^ ((n : ℝ) / 2) := by
  obtain ⟨A, hA, ha⟩ := compact_local_family_spatial_jets
    (isCompact_closedBall (0 : TransverseSpace d) 1) hcρ isOpen_gaussianPositiveRegion
    (fun p hp => ⟨hpos p.2 hp.2, gaussianB0_pos_of_small (by simpa using hp.1) (hv p.2 hp.2)⟩)
    contDiffOn_gaussianInverseAmplitude N
  obtain ⟨B, hB, hb⟩ := uniform_inverse_gaussian_phase_jets hcρ hpos 1 (RW + Rχ) N
  obtain ⟨D, hD, hd⟩ := radialAngularCutoff_jets hρ hcρ hχ hcχ hpos N
  let E := 2 ^ N * A * B
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨2 ^ N * D * E, by positivity, ?_⟩
  intro W hW L hL hRW n hn η
  have hs : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
  have hL0 : 0 ≤ L := by linarith
  by_cases hη : η ∈ tsupport ρ
  · by_cases hactive : ‖Real.sqrt L • gaussianVelocity η‖ ≤ Rχ
    · have hpatch : Real.sqrt L * ‖W - gaussianVelocity η‖ ≤ RW + Rχ := by
        have hactive' : Real.sqrt L * ‖gaussianVelocity η‖ ≤ Rχ := by
          simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg L)] using hactive
        calc
          _ ≤ Real.sqrt L * (‖W‖ + ‖gaussianVelocity η‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.sqrt_nonneg L)
          _ ≤ RW + Rχ := by nlinarith
      have hV : IsOpen {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ ∧ 0 < gaussianB0 (W, ξ)} :=
        isOpen_gaussianPositiveRegion.preimage (continuous_const.prodMk continuous_id)
      have ha' : ContDiffOn ℝ ∞ (fun ξ => gaussianInverseAmplitude (W, ξ))
          {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ ∧ 0 < gaussianB0 (W, ξ)} :=
        contDiffOn_gaussianInverseAmplitude.comp
          (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
      have hg := (contDiffOn_sourceInverseGaussian W hL0).mono
        (show {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ ∧ 0 < gaussianB0 (W, ξ)} ⊆
          {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ} from fun _ h => h.1)
      have hηV : 0 < gaussianFrequencyK η ∧ 0 < gaussianB0 (W, η) :=
        ⟨hpos η hη, gaussianB0_pos_of_small hW (hv η hη)⟩
      let f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ := fun ξ => gaussianInverseAmplitude (W, ξ) * Complex.exp
        ((L / 2 * gaussianFrequencyK ξ * ‖W - gaussianVelocity ξ‖ ^ 2 : ℝ))
      have hf : ContDiffOn ℝ ∞ f {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ ∧ 0 < gaussianB0 (W, ξ)} :=
        ha'.mul hg
      have hfb : ∀ q ≤ n, ‖iteratedFDeriv ℝ q f η‖ ≤ E * Real.sqrt L ^ q := by
        intro q hq
        have hbg : ∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun ξ : OAI.Analysis.Calculus.Current.SpatialSpace d => Complex.exp
            ((L / 2 * gaussianFrequencyK ξ * ‖W - gaussianVelocity ξ‖ ^ 2 : ℝ))) η‖ ≤
            B * Real.sqrt L ^ i := by
          intro i hi
          rw [sqrt_pow_eq_half_rpow hL0]
          exact hb W hW η hη L hL hpatch i ((hi.trans hq).trans hn)
        have hh := local_scaled_product_jets hV ha' hg hA hB (Real.sqrt_nonneg L) hηV q
          (fun i hi => (ha W (by simpa using hW) η hη i ((hi.trans hq).trans hn)).trans
            (le_mul_of_one_le_right hA (one_le_pow₀ hs)))
          hbg
        exact hh.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hq.trans hn)) hA) hB)
          (pow_nonneg (Real.sqrt_nonneg L) q))
      have hh := local_scaled_product_jets hV
        (contDiff_radialAngularCutoff hρ hχ hpos _).contDiffOn hf hD hE (Real.sqrt_nonneg L)
        hηV n (fun i hi => hd _ hs i (hi.trans hn) η) hfb
      have hh' := hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn) hD) hE)
        (pow_nonneg (Real.sqrt_nonneg L) n))
      have he : (fun ξ => radialAngularCutoff ρ χ (Real.sqrt L) ξ * f ξ) =
          gaussianInverseCore ρ χ L W := by
        funext ξ
        rfl
      rw [he, sqrt_pow_eq_half_rpow hL0] at hh'
      exact hh'
    · have hz : gaussianInverseCore ρ χ L W =ᶠ[𝓝 η] 0 := by
        filter_upwards [radialAngularCutoff_zero_near_large_velocity ρ hsupp
          (hpos η hη) (lt_of_not_ge hactive)] with ξ hξ
        simp [gaussianInverseCore, hξ]
      rw [(hz.iteratedFDeriv ℝ n).self_of_nhds]
      simp only [Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
      positivity
  · rw [((gaussianInverseCore_zero_near χ L W hη).iteratedFDeriv ℝ n).self_of_nhds]
    simp only [Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
    positivity

def gaussianInverseSymbol {d : ℕ} (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ)
    (χ : TransverseSpace d → ℂ) (h L : ℝ) (W : TransverseSpace d) : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ :=
  (h ^ d * L ^ ((d : ℝ) / 2)) • gaussianInverseCore ρ χ L W

/-- The normalized inverse symbols satisfy the exact output derivative
exponents `hᵈ L^((j+d)/2)` on the observation patch. -/
theorem gaussianInverseSymbol_jets {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ tsupport ρ, ‖gaussianVelocity η‖ ≤ 1)
    (Rχ RW : ℝ) (hsupp : tsupport χ ⊆ closedBall 0 Rχ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ 1 →
      ∀ h : ℝ, 0 < h → ∀ L : ℝ, 1 ≤ L → Real.sqrt L * ‖W‖ ≤ RW →
      ∀ n ≤ N, ∀ η, ‖iteratedFDeriv ℝ n (gaussianInverseSymbol ρ χ h L W) η‖ ≤
        C * h ^ d * L ^ (((n : ℝ) + d) / 2) := by
  obtain ⟨C, hC, hc⟩ := gaussianInverseCore_jets hρ hcρ hχ hcχ hpos hv Rχ RW hsupp N
  refine ⟨C, hC, ?_⟩
  intro W hW h hh L hL hRW n hn η
  have hL0 : 0 ≤ L := by linarith
  have hfac : 0 ≤ h ^ d * L ^ ((d : ℝ) / 2) := by positivity
  have he : L ^ ((d : ℝ) / 2) * L ^ ((n : ℝ) / 2) =
      L ^ (((n : ℝ) + d) / 2) := by
    rw [← Real.rpow_add (by linarith : 0 < L)]
    congr 1
    ring
  unfold gaussianInverseSymbol
  rw [iteratedFDeriv_const_smul_apply
    ((contDiff_gaussianInverseCore hρ hχ hpos hv hL0 W hW).of_le (by simp)).contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac]
  calc
    _ ≤ (h ^ d * L ^ ((d : ℝ) / 2)) * (C * L ^ ((n : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (hc W hW L hL hRW n hn η) hfac
    _ = C * h ^ d * L ^ (((n : ℝ) + d) / 2) := by
      rw [show (h ^ d * L ^ ((d : ℝ) / 2)) * (C * L ^ ((n : ℝ) / 2)) =
        C * h ^ d * (L ^ ((d : ℝ) / 2) * L ^ ((n : ℝ) / 2)) by ring, he]

end OAI.Analysis.PDE.Concentration
