import OAI.Analysis.Fourier.BochnerRiesz.Projection

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- A support-localized thin-shell estimate for arbitrary Schwartz input.
All analytic assumptions have been discharged by local smoothing; the
remaining hypotheses merely specify the two smooth cutoff supports. -/
theorem localSmoothing_projected_shell (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hzero : (0 : Space n) ∉ tsupport ψ)
    (hcover : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ s : ℝ,
      (∀ ξ : Space n, φ (s - ‖ξ‖) ≠ 0 → χ (h • ((2 * Real.pi) • ξ)) = 1) →
      ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s) (ENNReal.ofReal p) volume ∧
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA, ha⟩ := annularProject_uniform_bound hχ hcχ
  obtain ⟨B, hB, hb⟩ := localSmoothing_thinShellCycles hls hn hψ hcψ hzero φ hp hε
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  intro h hh hh1 s hcut f
  have H := hb h hh hh1 (annularProject χ h f)
    (annularProject_support_cutoff hχ hcχ hh f hcover) s
  have he : (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 (annularProject χ h f) x s) =
      (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s) := by
    funext x
    exact thinShellCycles_annularProject hχ hcχ hh φ 1 s f (by simpa only [div_one] using hcut) x
  rw [he] at H
  refine ⟨H.1, H.2.trans ?_⟩
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc
    _ ≤ ENNReal.ofReal (B * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
        (ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume) :=
      mul_le_mul' le_rfl (ha h hh f _ hp1 ENNReal.ofReal_ne_top)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end OAI.Analysis.Fourier.BochnerRiesz
