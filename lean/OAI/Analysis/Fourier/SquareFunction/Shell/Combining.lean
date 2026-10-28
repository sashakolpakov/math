import OAI.Analysis.Fourier.SquareFunction.Shell.Projection

open OAI.Analysis.Fourier.Wave

/-! The combining-dilates and annular Littlewood--Paley estimates applied
to the actual shell convolution operators. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ContDiff ENNReal

theorem combining_thinShellKernel_family {n N : ℕ} [NeZero n]
    {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hcut : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (hband : ∀ ξ, ψ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    (φ : SchwartzMap ℝ ℂ) {p : ℝ} (hp : 2 < p) :
    ∃ A : ℝ, 0 < A ∧ ∀ (s : Finset ℤ) (f : SchwartzMap (Space n) ℂ)
      {q C δ τ : ℝ}, (n : ℝ) + 1 < q → 0 ≤ C → 0 < τ → τ ≤ 1 →
      (∀ u, ‖thinShellKernel χ hχ.continuous φ δ u‖ ≤
        (C * τ ^ (-q)) * (‖u‖ + 1) ^ (-q)) →
      (∀ u, ‖fderiv ℝ (thinShellKernel χ hχ.continuous φ δ) u‖ ≤
        (C * τ ^ (-q)) * (‖u‖ + 1) ^ (-q)) →
      ∀ {B₂ Bₚ : ℝ≥0∞}, B₂ ≠ ⊤ →
      (∀ g : Space n → ℂ, Integrable g → MemLp g 2 volume →
        eLpNorm (convolveKernel (thinShellKernel χ hχ.continuous φ δ) g) 2 volume ≤
          B₂ * eLpNorm g 2 volume) →
      (∀ g : Space n → ℂ, Integrable g → MemLp g (ENNReal.ofReal p) volume →
        eLpNorm (convolveKernel (thinShellKernel χ hχ.continuous φ δ) g)
          (ENNReal.ofReal p) volume ≤ Bₚ * eLpNorm g (ENNReal.ofReal p) volume) →
      eLpNorm (fun x => vectorNorm (fun i : s =>
        convolveKernel (dilatedKernel (thinShellKernel χ hχ.continuous φ δ)
          ((2 : ℝ) ^ i.val)) f x)) (ENNReal.ofReal p) volume ≤
        ((combiningLogConstant n p q *
          (ENNReal.ofReal (C * τ) + ENNReal.ofReal (1 + Real.log (1 / τ)) ^
            (1 / 2 - 1 / p) * Bₚ + B₂)) * ENNReal.ofReal A) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  let : MeasurableSpace RadiusHilbert := borel RadiusHilbert
  let : BorelSpace RadiusHilbert := ⟨rfl⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨A, hA, hLP⟩ := OAI.Analysis.Fourier.BochnerRiesz.littlewoodPaley_annular_projection hψ hcψ hband hp
  refine ⟨A, hA, ?_⟩
  intro s f q C δ τ hq hC hτ hτone hK hK' B₂ Bₚ hB₂ h2 hP
  let g : s → SchwartzMap (Space n) ℂ := fun i =>
    OAI.Analysis.Fourier.BochnerRiesz.annularProject ψ ((2 : ℝ) ^ (-i.val)) f
  have hgb (i : s) : BddAbove (range fun x => ‖g i x‖) := by
    refine ⟨SchwartzMap.seminorm ℝ 0 0 (g i), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact SchwartzMap.norm_le_seminorm ℝ (g i) x
  have hb := combining_normalized_dilates s
    (thinShellKernel χ hχ.continuous φ δ) (fun i => g i) hp hq hC hτ hτone
    (differentiable_thinShellKernel χ hχ.continuous hcχ φ δ) hK hK'
    (fun i => (g i).continuous.measurable) (fun i => (g i).integrable) hgb
    (fun i => (g i).memLp 2) (fun i => (g i).memLp (ENNReal.ofReal p)) hB₂ h2 hP
  have he : (fun x => vectorNorm (fun i : s =>
      convolveKernel (dilatedKernel (thinShellKernel χ hχ.continuous φ δ)
        ((2 : ℝ) ^ i.val)) (g i) x)) =
    (fun x => vectorNorm (fun i : s =>
      convolveKernel (dilatedKernel (thinShellKernel χ hχ.continuous φ δ)
        ((2 : ℝ) ^ i.val)) f x)) := by
    funext x
    congr 1
    funext i
    simpa only [g, zpow_neg] using
      convolve_dilated_thinShellKernel_annularProject hχ hcχ hψ hcψ hcut φ δ
        (a := (2 : ℝ) ^ i.val) (by positivity) f x
  rw [he] at hb
  exact hb.trans (by
    simpa only [mul_assoc] using mul_le_mul' (le_refl
      (combiningLogConstant n p q *
        (ENNReal.ofReal (C * τ) + ENNReal.ofReal (1 + Real.log (1 / τ)) ^
          (1 / 2 - 1 / p) * Bₚ + B₂))) (hLP s f))

end OAI.Analysis.Fourier.SquareFunction
