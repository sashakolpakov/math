import OAI.Analysis.Fourier.SquareFunction.Shell.Mixed

open OAI.Analysis.Fourier.Wave

/-! The mixed thin-shell bound obtained from Euclidean local smoothing. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff

theorem shell_time_factor {δ A C p σ : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hp : 2 ≤ p) (D : ℝ≥0∞) :
    (ENNReal.ofReal (δ * A) * (ENNReal.ofReal δ⁻¹ * D) ^ (1 / 2 - 1 / p)) *
        ENNReal.ofReal (C * δ ^ (-σ - 1 / p)) =
      (ENNReal.ofReal (A * C) * D ^ (1 / 2 - 1 / p)) *
        ENNReal.ofReal (δ ^ (1 / 2 - σ)) := by
  let θ : ℝ := 1 / 2 - 1 / p
  have hθ : 0 ≤ θ := by
    have hdiv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
    dsimp only [θ]
    linarith
  have he : δ * A * δ ^ (-θ) * (C * δ ^ (-σ - 1 / p)) = (A * C) * δ ^ (1 / 2 - σ) := by
    calc
      _ = (A * C) * (δ ^ (1 : ℝ) * δ ^ (-θ) * δ ^ (-σ - 1 / p)) := by rw [Real.rpow_one]; ring
      _ = (A * C) * δ ^ ((1 : ℝ) + (-θ) + (-σ - 1 / p)) := by rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
      _ = _ := by congr 2; dsimp only [θ]; ring
  change (ENNReal.ofReal (δ * A) * (ENNReal.ofReal δ⁻¹ * D) ^ θ) *
    ENNReal.ofReal (C * δ ^ (-σ - 1 / p)) = _
  rw [ENNReal.mul_rpow_of_nonneg _ _ hθ,
    ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hδ), Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le]
  calc
    _ = (ENNReal.ofReal (δ * A) * ENNReal.ofReal (δ ^ (-θ)) *
        ENNReal.ofReal (C * δ ^ (-σ - 1 / p))) * D ^ θ := by ac_rfl
    _ = ENNReal.ofReal (δ * A * δ ^ (-θ) * (C * δ ^ (-σ - 1 / p))) * D ^ θ := by
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hδ.le hA) (Real.rpow_nonneg hδ.le _)),
        ENNReal.ofReal_mul (mul_nonneg hδ.le hA)]
    _ = _ := by rw [he, ENNReal.ofReal_mul (mul_nonneg hA hC)]; ac_rfl

/-- The actual all-radius shell operator maps an annular input into
`Lᵖ_x L²_s` with the gain `δ^(1/2-σ)`, where `σ=s_+(p)+ε`.
All auxiliary time weights have been eliminated from this statement. -/
theorem localSmoothing_thinShell_mixed (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ ξ = 1) →
      MemLp (thinShellSquareNorm φ δ f) (ENNReal.ofReal p) volume ∧
      eLpNorm (thinShellSquareNorm φ δ f) (ENNReal.ofReal p) volume ≤
        (C * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  let σ := OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε
  let M := 1 / p + σ + 1
  have hM : 1 / p + (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) < M := by dsimp only [M, σ]; linarith
  obtain ⟨C₀, hC₀, htime⟩ := OAI.Analysis.Fourier.BochnerRiesz.localSmoothing_shell_time hls hn hχ hc hzero hp hε hM
  obtain ⟨A, hA, hdec⟩ := OAI.Analysis.Fourier.BochnerRiesz.schwartz_time_decay (𝓕 φ : SchwartzMap ℝ ℂ) M
  let D := ∫⁻ t : ℝ, OAI.Analysis.Fourier.BochnerRiesz.timeDensity t
  let C := ENNReal.ofReal (A * C₀) * D ^ (1 / 2 - 1 / p)
  have hθ : 0 ≤ 1 / 2 - 1 / p := by
    have hdiv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
    linarith
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hθ OAI.Analysis.Fourier.BochnerRiesz.lintegral_timeDensity_lt_top.ne)
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδone f hcut
  let F := fun z : Space n × ℝ => (1 + |δ * z.2|) ^ (-M) • OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1
  have hF : Measurable F := by
    have hw : Continuous (fun z : Space n × ℝ => (1 + |δ * z.2|) ^ (-M)) := by
      apply Continuous.rpow_const (by fun_prop)
      intro z
      left
      positivity
    exact hw.measurable.smul (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).measurable
  have hk : Measurable (fun t : ℝ => OAI.Analysis.Fourier.BochnerRiesz.timeDensity (δ * t)) :=
    OAI.Analysis.Fourier.BochnerRiesz.measurable_timeDensity.comp (measurable_const.mul measurable_id)
  have hs := eLpNorm_of_weighted_time_square_domination hp hk
    (fun t => OAI.Analysis.Fourier.BochnerRiesz.timeDensity_le_one (δ * t)) hF
    (measurable_thinShellSquareNorm φ hδ f).aestronglyMeasurable
    (thinShell_square_decay_domination φ hδ hA.le hdec f)
  rw [lintegral_timeDensity_dilate hδ] at hs
  have ht := (htime δ hδ hδone f hcut).2
  have hnorm : eLpNorm (thinShellSquareNorm φ δ f) (ENNReal.ofReal p) volume ≤
      (C * ENNReal.ofReal (δ ^ (1 / 2 - σ))) * eLpNorm f (ENNReal.ofReal p) volume := by
    calc
      _ ≤ (ENNReal.ofReal (δ * A) * (ENNReal.ofReal δ⁻¹ * D) ^ (1 / 2 - 1 / p)) *
          eLpNorm F (ENNReal.ofReal p) (volume.prod volume) := hs
      _ ≤ (ENNReal.ofReal (δ * A) * (ENNReal.ofReal δ⁻¹ * D) ^ (1 / 2 - 1 / p)) *
          (ENNReal.ofReal (C₀ * δ ^ (-σ - 1 / p)) * eLpNorm f (ENNReal.ofReal p) volume) :=
        mul_le_mul_right ht _
      _ = _ := by rw [← mul_assoc, shell_time_factor hδ hA.le hC₀.le hp D]
  refine ⟨?_, hnorm⟩
  exact hnorm.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) ENNReal.ofReal_lt_top)
    (f.memLp (ENNReal.ofReal p)).eLpNorm_lt_top)

end OAI.Analysis.Fourier.SquareFunction
