import OAI.Analysis.Fourier.BochnerRiesz.Shell.Domination

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- The fixed-dilation thin-annulus estimate from local smoothing. The
radius is arbitrary; the input is localized to frequency `h⁻¹`. -/
theorem localSmoothing_thinShellCycles (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) → ∀ s : ℝ,
      MemLp (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s) (ENNReal.ofReal p) volume ∧
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) * eLpNorm f (ENNReal.ofReal p) volume := by
  let M := 1 / p + (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) + 1
  have hM : 1 / p + (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) < M := by dsimp [M]; linarith
  obtain ⟨B, hB, hb⟩ := localSmoothing_weighted_all_time hls hn hχ hc hzero hp hε hM
  obtain ⟨A, hA, ha⟩ := thinShellCycles_weighted_domination φ M
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
  intro h hh hhone f hcut s
  have hp1 : 1 ≤ p := by linarith
  have H := eLpNorm_of_weighted_time_domination hp1 measurable_timeDensity timeDensity_le_one
    (continuous_weightedTimeFunction M (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f)).measurable
    (continuous_thinShellCycles_space φ 1 f s).aestronglyMeasurable (ha n f s)
  have HL := (hb h hh hhone f hcut).2
  have HF : eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s) (ENNReal.ofReal p) volume ≤
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
