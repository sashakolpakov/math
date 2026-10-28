import OAI.Analysis.Fourier.BochnerRiesz.AllTime

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def scaledWeightedTimeFunction {n : ℕ} (M R : ℝ) (F : Space n × ℝ → ℂ)
    (z : Space n × ℝ) : ℂ := (1 + |z.2 / R|) ^ (-M) • F z

theorem continuous_scaledWeightedTimeFunction {n : ℕ} (M R : ℝ) {F : Space n × ℝ → ℂ}
    (hF : Continuous F) : Continuous (scaledWeightedTimeFunction M R F) := by
  change Continuous ((fun z : Space n × ℝ ↦ (1 + |z.2 / R|) ^ (-M)) • F)
  apply Continuous.smul _ hF
  apply Continuous.rpow_const (by fun_prop)
  intro z
  exact Or.inl (by positivity)

/-- Arbitrary time-scale version of the all-time annular local-smoothing
bound. In shell applications `h=1` and `R=δ⁻¹`. -/
theorem localSmoothing_weighted_time_scale (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {p ε M : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (hM : 1 / p + (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ h R : ℝ, 0 < h → h ≤ R →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      MemLp (scaledWeightedTimeFunction M R (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
        (ENNReal.ofReal p) (volume.prod volume) ∧
      eLpNorm (scaledWeightedTimeFunction M R (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
        (ENNReal.ofReal p) (volume.prod volume) ≤
      ENNReal.ofReal (C * R ^ (1 / p) * (h / R) ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
        eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := localSmoothing_weighted_all_time hls hn hχ hc hzero hp hε hM
  refine ⟨C, hC, ?_⟩
  intro h R hh hhr f hcut
  have hR : 0 < R := lt_of_lt_of_le hh hhr
  let g := schwartzDilate R hR.ne' f
  have hcutg : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ ≠ 0 → χ ((h / R) • ξ) = 1 := by
    intro ξ hξ
    have hnz : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (R⁻¹ • ξ) ≠ 0 := by
      intro hz
      apply hξ
      change OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f (R • x)) ξ = 0
      rw [angularFourier_dilate f hR, hz, smul_zero]
    simpa only [smul_smul, div_eq_mul_inv] using hcut (R⁻¹ • ξ) hnz
  have hg := (hb (h / R) (div_pos hh hR) ((div_le_one hR).mpr hhr) g hcutg).2
  let F : Space n × ℝ → ℂ := scaledWeightedTimeFunction M R
    (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
  have hF : Continuous F := continuous_scaledWeightedTimeFunction M R (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f)
  have heq : weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 g z.1) =
      (fun z : Space n × ℝ ↦ F (R • z.1, R * z.2)) := by
    funext z
    change (1 + |z.2|) ^ (-M) • OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (fun x ↦ f (R • x)) z.1 = _
    rw [halfWaveIntegral_dilate f hR]
    simp [F, scaledWeightedTimeFunction, mul_div_cancel_left₀ _ hR.ne']
  rw [heq, eLpNorm_spacetime_dilate_univ F hF.measurable _ hR,
    eLpNorm_schwartzDilate f _ hR] at hg
  simp only [ENNReal.toReal_ofReal (show 0 ≤ p by linarith)] at hg
  let D : ℝ≥0∞ := ENNReal.ofReal ((R ^ (n + 1))⁻¹) ^ (1 / p)
  have hD : D ≠ 0 := by dsimp [D]; positivity
  have hDt : D ≠ ⊤ := by dsimp [D]; finiteness
  have H : eLpNorm F (ENNReal.ofReal p) (volume.prod volume) ≤
      ENNReal.ofReal (C * R ^ (1 / p) * (h / R) ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
        eLpNorm f (ENNReal.ofReal p) volume := by
    apply (ENNReal.mul_le_mul_iff_right hD hDt).mp
    calc
      _ ≤ ENNReal.ofReal (C * (h / R) ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
          (ENNReal.ofReal ((R ^ n)⁻¹) ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) volume) := hg
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg hR.le _)),
          ENNReal.ofReal_mul hC.le, ENNReal.ofReal_mul hC.le]
        rw [← spacetime_dilation_factor hR (1 / p)]
        dsimp [D]
        ac_rfl
  refine ⟨?_, H⟩
  exact H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top)

end OAI.Analysis.Fourier.BochnerRiesz
