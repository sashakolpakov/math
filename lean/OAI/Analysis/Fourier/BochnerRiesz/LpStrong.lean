import OAI.Analysis.Fourier.BochnerRiesz.StrongConvergence

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


def brLpRadius {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : Ioi (0 : ℝ) → BrLp n p →L[ℂ] BrLp n p) (R : ℝ) : BrLp n p →L[ℂ] BrLp n p :=
  if h : 0 < R then T ⟨R, h⟩ else 0

theorem tendsto_brLpRadius_of_core {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ⊤) {δ : ℝ} (T : Ioi (0 : ℝ) → BrLp n p →L[ℂ] BrLp n p)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ R, ‖T R‖ ≤ C)
    (hs : ∀ R (f : SchwartzMap (Space n) ℂ),
      (T R (f.toLp p volume) : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R.val f)
    (hc : ∀ f : SchwartzMap (Space n) ℂ,
      Tendsto (fun R : ℝ => eLpNorm (fun x => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x - f x) p volume) atTop (𝓝 0))
    (f : BrLp n p) :
    Tendsto (fun R : ℝ => brLpRadius T R f) atTop (𝓝 f) := by
  apply tendsto_operators_of_dense_core
    (show DenseRange (fun g : SchwartzMap (Space n) ℂ => g.toLp p volume) from
      SchwartzMap.denseRange_toLpCLM hpt) (brLpRadius T) hC
  · apply Eventually.of_forall
    intro R
    by_cases hR : 0 < R
    · simpa only [brLpRadius, dite_eq_left hR] using hT ⟨R, hR⟩
    · simpa only [brLpRadius, dite_eq_right hR, norm_zero] using hC
  · intro g
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
    apply (hc g).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    apply eLpNorm_congr_ae
    filter_upwards [hs ⟨R, hR⟩ g, (g.memLp p volume).coeFn_toLp] with x hx hg
    change OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R g x - g x = brLpRadius T R (g.toLp p volume) x - g.toLp p volume x
    simp only [brLpRadius, dite_eq_left hR]
    rw [hx]
    exact congrArg (fun z => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R g x - z) hg.symm

/-- Every finite exponent strictly above one has genuine bounded
Bochner--Riesz operators converging strongly to the identity. -/
theorem localSmoothing_bochnerRiesz_Lp_strong_convergence (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (hδ : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal p) < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : Ioi (0 : ℝ) →
        BrLp n (ENNReal.ofReal p) →L[ℂ] BrLp n (ENNReal.ofReal p),
      (∀ R, ‖T R‖ ≤ C) ∧
      (∀ R (f : SchwartzMap (Space n) ℂ),
        (T R (f.toLp (ENNReal.ofReal p) volume) : Space n → ℂ) =ᵐ[volume]
          OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R.val f) ∧
      (∀ f, Tendsto (fun R : ℝ => brLpRadius T R f) atTop (𝓝 f)) := by
  obtain ⟨C, hC, T, hT, hs⟩ := localSmoothing_bochnerRiesz_Lp_operators hls hn ENNReal.ofReal_ne_top hδ
  refine ⟨C, hC, T, hT, hs, ?_⟩
  exact tendsto_brLpRadius_of_core ENNReal.ofReal_ne_top T hC.le hT hs
    (localSmoothing_bochnerRiesz_schwartz_norm_convergence hls hn hp hδ)

end OAI.Analysis.Fourier.BochnerRiesz
