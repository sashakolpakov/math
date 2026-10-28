import OAI.Analysis.Fourier.BochnerRiesz.Shell.Bound

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem schwartz_time_decay_uniform_dilation (φ : SchwartzMap ℝ ℂ) (M : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ δ ∈ Icc (1 / 2 : ℝ) 1, ∀ t : ℝ,
      ‖(δ : ℂ) * φ (δ * t)‖ ≤ A * (1 + |t|) ^ (-2 : ℝ) * (1 + |t|) ^ (-M) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (M + 2)
  let B : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) φ
  have hB : 0 ≤ B := by positivity
  refine ⟨2 ^ N * B + 1, by positivity, ?_⟩
  intro δ hδ t
  have hδ0 : 0 < δ := by linarith [hδ.1]
  have hb : (1 + |δ * t|) ^ N * ‖φ (δ * t)‖ ≤ B := by
    simpa [B] using SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl φ (δ * t)
  have ht : 1 + |t| ≤ 2 * (1 + |δ * t|) := by
    rw [abs_mul, abs_of_pos hδ0]
    nlinarith [hδ.1, abs_nonneg t]
  have hp : (1 + |t|) ^ N ≤ 2 ^ N * (1 + |δ * t|) ^ N := by
    calc
      _ ≤ (2 * (1 + |δ * t|)) ^ N := pow_le_pow_left₀ (by positivity) ht N
      _ = _ := mul_pow _ _ _
  have hc : ‖(δ : ℂ) * φ (δ * t)‖ ≤ ‖φ (δ * t)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
    exact mul_le_of_le_one_left (norm_nonneg _) hδ.2
  have hd : (1 + |t|) ^ N * ‖(δ : ℂ) * φ (δ * t)‖ ≤ 2 ^ N * B := by
    calc
      _ ≤ (2 ^ N * (1 + |δ * t|) ^ N) * ‖φ (δ * t)‖ :=
        mul_le_mul hp hc (norm_nonneg _) (by positivity)
      _ ≤ 2 ^ N * B := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hb (by positivity)
  have ht0 : 0 < 1 + |t| := by positivity
  have he : ‖(δ : ℂ) * φ (δ * t)‖ ≤
      (2 ^ N * B + 1) * (1 + |t|) ^ (-(N : ℝ)) := by
    rw [Real.rpow_neg ht0.le, Real.rpow_natCast, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos ht0 N)).mpr
    nlinarith
  calc
    _ ≤ (2 ^ N * B + 1) * (1 + |t|) ^ (-(N : ℝ)) := he
    _ ≤ (2 ^ N * B + 1) * (1 + |t|) ^ ((-2 : ℝ) + (-M)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
    _ = _ := by rw [Real.rpow_add ht0]; ring

theorem enorm_thinShellCycles_le_time_dilation {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) (s : ℝ) (x : Space n) :
    ‖OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ δ f x s‖ₑ ≤
      ∫⁻ t : ℝ, ‖(δ : ℂ) * (𝓕 φ : SchwartzMap ℝ ℂ) (δ * t)‖ₑ * ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ := by
  rw [thinShellCycles_eq_wave_integral φ hδ f x s]
  calc
    _ ≤ ∫⁻ t : ℝ, ‖Complex.exp ((2 * Real.pi * t * s : ℝ) * Complex.I) *
        ((δ : ℂ) * (𝓕 φ : SchwartzMap ℝ ℂ) (δ * t) * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = _ := by
      apply lintegral_congr
      intro t
      have he : ‖Complex.exp ((2 * Real.pi * t * s : ℝ) * Complex.I)‖ₑ = 1 := by
        rw [← ofReal_norm]
        simp [Complex.norm_exp]
      rw [enorm_mul, he, one_mul, enorm_mul]

/-- The maximal thin-shell operator over arbitrary centers and a compact
interval of shell widths. The supremum is taken in the extended nonnegative
reals, before any integrability has been proved. -/
def localThinShellMax {n : ℕ} (φ : SchwartzMap ℝ ℂ) (f : SchwartzMap (Space n) ℂ)
    (x : Space n) : ℝ≥0∞ :=
  ⨆ s : ℝ, ⨆ δ : Icc (1 / 2 : ℝ) 1, ‖OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ δ.val f x s‖ₑ

theorem measurable_localThinShellMax {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    (f : SchwartzMap (Space n) ℂ) : Measurable (localThinShellMax φ f) := by
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_iSup
  intro s
  apply lowerSemicontinuous_iSup
  intro δ
  exact (continuous_thinShellCycles_space φ δ.val f s).enorm.lowerSemicontinuous

theorem localThinShellMax_weighted_domination (φ : SchwartzMap ℝ ℂ) (M : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (f : SchwartzMap (Space n) ℂ) (x : Space n),
      localThinShellMax φ f x ≤ ENNReal.ofReal A *
        ∫⁻ t : ℝ, timeDensity t *
          ‖weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) (x, t)‖ₑ := by
  obtain ⟨A, hA, hb⟩ := schwartz_time_decay_uniform_dilation (𝓕 φ : SchwartzMap ℝ ℂ) M
  refine ⟨A, hA, ?_⟩
  intro n f x
  apply iSup_le
  intro s
  apply iSup_le
  intro δ
  have hδ : 0 < δ.val := by linarith [δ.property.1]
  calc
    _ ≤ ∫⁻ t : ℝ, ‖(δ.val : ℂ) * (𝓕 φ : SchwartzMap ℝ ℂ) (δ.val * t)‖ₑ *
        ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ := enorm_thinShellCycles_le_time_dilation φ hδ f s x
    _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal A * (timeDensity t *
        ‖weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) (x, t)‖ₑ) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [enorm_weightedTimeFunction]
      have hd : ‖(δ.val : ℂ) * (𝓕 φ : SchwartzMap ℝ ℂ) (δ.val * t)‖ₑ ≤
          ENNReal.ofReal A * timeDensity t * ENNReal.ofReal ((1 + |t|) ^ (-M)) := by
        rw [← ofReal_norm]
        calc
          _ ≤ ENNReal.ofReal (A * (1 + |t|) ^ (-2 : ℝ) * (1 + |t|) ^ (-M)) :=
            ENNReal.ofReal_le_ofReal (hb δ.val δ.property t)
          _ = _ := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hA.le]
            rfl
      simpa only [mul_assoc] using mul_le_mul' hd (le_refl ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ)
    _ = _ := by
      apply lintegral_const_mul''
      exact measurable_timeDensity.aemeasurable.mul
        (measurable_weightedTime_slice f M x).enorm.aemeasurable

/-- Local smoothing controls the supremum over all shell centers and
all widths between `1/2` and `1`, for annularly supported input. -/
theorem localSmoothing_localThinShellMax (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      MemLp (localThinShellMax φ f) (ENNReal.ofReal p) volume ∧
      eLpNorm (localThinShellMax φ f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) * eLpNorm f (ENNReal.ofReal p) volume := by
  let M := 1 / p + (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) + 1
  have hM : 1 / p + (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) < M := by dsimp [M]; linarith
  obtain ⟨B, hB, hb⟩ := localSmoothing_weighted_all_time hls hn hχ hc hzero hp hε hM
  obtain ⟨A, hA, ha⟩ := localThinShellMax_weighted_domination φ M
  let D : ℝ≥0∞ := ENNReal.ofReal A * (∫⁻ t : ℝ, timeDensity t) ^ ((p - 1) / p)
  have hpexp : 0 ≤ (p - 1) / p := div_nonneg (by linarith) (by linarith)
  have hD : D ≠ ⊤ := by
    apply ne_of_lt
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact ENNReal.rpow_lt_top_of_nonneg hpexp lintegral_timeDensity_lt_top.ne
  have hDle : D ≤ ENNReal.ofReal (D.toReal + 1) := by
    calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ ENNReal.ofReal (D.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨(D.toReal + 1) * B, mul_pos (by positivity) hB, ?_⟩
  intro h hh hhone f hcut
  have hp1 : 1 ≤ p := by linarith
  have H := eLpNorm_of_weighted_time_domination hp1 measurable_timeDensity timeDensity_le_one
    (continuous_weightedTimeFunction M (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f)).measurable
    (measurable_localThinShellMax φ f).aestronglyMeasurable (fun x ↦ by
      simpa only [enorm_eq_self] using ha n f x)
  have HL := (hb h hh hhone f hcut).2
  have HF : eLpNorm (localThinShellMax φ f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((D.toReal + 1) * B * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
        eLpNorm f (ENNReal.ofReal p) volume := by
    calc
      _ ≤ D * eLpNorm (weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
          (ENNReal.ofReal p) (volume.prod volume) := H
      _ ≤ ENNReal.ofReal (D.toReal + 1) *
          (ENNReal.ofReal (B * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) * eLpNorm f (ENNReal.ofReal p) volume) :=
        mul_le_mul' hDle HL
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
  exact ⟨HF.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top), HF⟩

end OAI.Analysis.Fourier.BochnerRiesz
