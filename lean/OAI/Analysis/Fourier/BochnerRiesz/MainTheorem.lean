import OAI.Analysis.Fourier.BochnerRiesz.Summability

open OAI.Analysis.Fourier.Wave

/-!
The complete Bochner--Riesz theorem from `sections/introduction.tex`.
The operators act on the whole `Lᵖ` space, not just its Schwartz core.
The maximal clause uses one coherent representative for every positive radius.
-/

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- Uniform boundedness in the strict Bochner--Riesz range, together with
strong convergence for every finite exponent (including `p = 1`). -/
def BochnerRieszUniformLp : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p : ℝ≥0∞, ∀ [Fact (1 ≤ p)], ∀ δ : ℝ,
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n p < δ →
    ∃ C : ℝ, 0 < C ∧ ∃ T : Ioi (0 : ℝ) → OAI.Analysis.Fourier.BochnerRiesz.BrLp n p →L[ℂ] OAI.Analysis.Fourier.BochnerRiesz.BrLp n p,
      (∀ R, ‖T R‖ ≤ C) ∧
      (∀ R (f : SchwartzMap (Space n) ℂ),
        (T R (f.toLp p volume) : Space n → ℂ) =ᵐ[volume]
          OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R.val f) ∧
      (p ≠ ⊤ → ∀ f, Tendsto (fun R : ℝ => OAI.Analysis.Fourier.BochnerRiesz.brLpRadius T R f) atTop (𝓝 f))

/-- Maximal boundedness and almost-everywhere convergence on the whole
`Lᵖ` space in the strict local-smoothing range. -/
def BochnerRieszMaximalLp : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p δ : ℝ, 2 ≤ p → ∀ [Fact (1 ≤ ENNReal.ofReal p)],
    OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ →
    ∃ C : ℝ, 0 < C ∧
    ∃ W : OAI.Analysis.Fourier.BochnerRiesz.BrLp n (ENNReal.ofReal p) →L[ℂ] OAI.Analysis.Fourier.BochnerRiesz.BrBoundedLp n (ENNReal.ofReal p),
      ‖W‖ ≤ C ∧
      (∀ f : SchwartzMap (Space n) ℂ, ∀ᵐ x ∂volume, ∀ R : ℝ, 0 < R →
        OAI.Analysis.Fourier.BochnerRiesz.brFullRepresentative (W (f.toLp (ENNReal.ofReal p) volume)) R x =
          OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x) ∧
      (∀ f : OAI.Analysis.Fourier.BochnerRiesz.BrLp n (ENNReal.ofReal p),
        Measurable (OAI.Analysis.Fourier.BochnerRiesz.brFullMaximal (W f)) ∧
        eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.brFullMaximal (W f)) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal C * ‖f‖ₑ) ∧
      (∀ f, Tendsto (fun R => OAI.Analysis.Fourier.BochnerRiesz.brFullEval R (W f)) atTop (𝓝 f)) ∧
      (∀ f, ∀ᵐ x ∂volume,
        Tendsto (fun R => OAI.Analysis.Fourier.BochnerRiesz.brFullRepresentative (W f) R x) atTop (𝓝 (f x)))

/-- All clauses of Theorem `thm:bochner-riesz`. -/
def BochnerRieszMainTheorem : Prop := BochnerRieszUniformLp ∧ BochnerRieszMaximalLp

theorem bochnerRieszUniformLp_of_localSmoothing (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) :
    BochnerRieszUniformLp := by
  intro n hn p hp δ hδ
  by_cases hpt : p = ⊤
  · obtain ⟨C, hC, T, hT, hs⟩ :=
      OAI.Analysis.Fourier.BochnerRiesz.localSmoothing_bochnerRiesz_all_Lp_operators hls hn hδ
    exact ⟨C, hC, T, hT, hs, fun hne => (hne hpt).elim⟩
  · obtain ⟨C, hC, T, hT, hs, hc⟩ :=
      OAI.Analysis.Fourier.BochnerRiesz.localSmoothing_bochnerRiesz_norm_summability hls hn hpt hδ
    exact ⟨C, hC, T, hT, hs, fun _ => hc⟩

theorem bochnerRieszMaximalLp_of_localSmoothing (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) :
    BochnerRieszMaximalLp := by
  intro n hn p δ hp hpFact hδ
  exact OAI.Analysis.Fourier.BochnerRiesz.localSmoothing_bochnerRiesz_Lp_full_summability hls hn hp hδ

theorem bochnerRieszMainTheorem_of_localSmoothing (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) :
    BochnerRieszMainTheorem :=
  ⟨bochnerRieszUniformLp_of_localSmoothing hls,
    bochnerRieszMaximalLp_of_localSmoothing hls⟩

end OAI.Analysis.Fourier.BochnerRiesz
