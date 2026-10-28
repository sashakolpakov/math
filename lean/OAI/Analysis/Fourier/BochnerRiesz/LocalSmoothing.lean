import OAI.Analysis.Fourier.BochnerRiesz.Annular
import OAI.Analysis.Fourier.BochnerRiesz.TimeDilation
import OAI.Analysis.Fourier.LocalSmoothing.L2

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- The local-smoothing hypothesis on genuine annular data, with its Sobolev
norm replaced by the sharp positive-loss frequency power. -/
theorem localSmoothing_annular_unit (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal (C * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
        eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA, ha⟩ := hls n hn p ε hp (Or.inl hε)
  obtain ⟨B, hB, hb⟩ := annular_besselPotential_bound hχ hc hzero (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)
  refine ⟨A * (B + 1), mul_pos hA (by linarith), ?_⟩
  intro h hh hone f hcut
  have hpone : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  calc
    _ ≤ ENNReal.ofReal A * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) f)
        (ENNReal.ofReal p) volume := (ha f).2.2
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal (B * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
        eLpNorm f (ENNReal.ofReal p) volume) :=
      mul_le_mul' le_rfl (hb h hh hone f f.integrable hcut _ hpone ENNReal.ofReal_ne_top)
    _ = ENNReal.ofReal (A * B * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
        eLpNorm f (ENNReal.ofReal p) volume := by
      rw [ENNReal.ofReal_mul (mul_nonneg hA.le hB),
        ENNReal.ofReal_mul hB, ENNReal.ofReal_mul hA.le]
      ac_rfl
    _ ≤ _ := by gcongr; linarith

/-- The exact rescaled annular estimate on a positive dyadic time slab. -/
theorem localSmoothing_annular_slab (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ h r : ℝ, 0 < h → h ≤ r →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (timeSlabMeasure n r) ≤
      ENNReal.ofReal (C * r ^ (1 / p) * (h / r) ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
        eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := localSmoothing_annular_unit hls hn hχ hc hzero hp hε
  refine ⟨C, hC, ?_⟩
  intro h r hh hhr f hcut
  have hr : 0 < r := lt_of_lt_of_le hh hhr
  let g := schwartzDilate r hr.ne' f
  have hcutg : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ ≠ 0 → χ ((h / r) • ξ) = 1 := by
    intro ξ hξ
    have hnz : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (r⁻¹ • ξ) ≠ 0 := by
      intro hz
      apply hξ
      change OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f (r • x)) ξ = 0
      rw [angularFourier_dilate f hr, hz, smul_zero]
    simpa only [smul_smul, div_eq_mul_inv] using hcut (r⁻¹ • ξ) hnz
  have hg := hb (h / r) (div_pos hh hr) ((div_le_one hr).mpr hhr) g hcutg
  have heq : (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 g z.1) =
      (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (r * z.2) f (r • z.1)) := by
    funext z
    exact halfWaveIntegral_dilate f hr z.2 z.1
  rw [heq, eLpNorm_spacetime_dilate _ (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).measurable _ hr,
    eLpNorm_schwartzDilate f _ hr] at hg
  simp only [ENNReal.toReal_ofReal (show 0 ≤ p by linarith)] at hg
  let D : ℝ≥0∞ := ENNReal.ofReal ((r ^ (n + 1))⁻¹) ^ (1 / p)
  have hD : D ≠ 0 := by dsimp [D]; positivity
  have hDt : D ≠ ⊤ := by dsimp [D]; finiteness
  apply (ENNReal.mul_le_mul_iff_right hD hDt).mp
  calc
    _ ≤ ENNReal.ofReal (C * (h / r) ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
        (ENNReal.ofReal ((r ^ n)⁻¹) ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) volume) := hg
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg hr.le _)),
        ENNReal.ofReal_mul hC.le, ENNReal.ofReal_mul hC.le]
      rw [← spacetime_dilation_factor hr (1 / p)]
      dsimp [D]
      ac_rfl

end OAI.Analysis.Fourier.BochnerRiesz
