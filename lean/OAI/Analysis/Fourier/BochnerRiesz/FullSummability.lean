import OAI.Analysis.Fourier.BochnerRiesz.FamilyCompatibility

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


def brFullEval {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (R : ℝ) :
    BrBoundedLp n p →L[ℂ] BrLp n p := if h : 0 < R then brBoundedEval ⟨R, h⟩ else 0

theorem brFullEval_coe {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (R : ℝ) (F : BrBoundedLp n p) :
    (brFullEval R F : Space n → ℂ) =ᵐ[volume] brFullRepresentative F R := by
  by_cases hR : 0 < R
  · simp only [brFullEval, dite_eq_left hR]
    filter_upwards [brBoundedEval_coe ⟨R, hR⟩ F] with x hx
    simpa only [brFullRepresentative, dite_eq_left hR] using hx
  · simp only [brFullEval, dite_eq_right hR, zero_apply]
    filter_upwards [Lp.coeFn_zero ℂ (μ := (volume : Measure (Space n))) (p := p)] with x hx
    simpa only [brFullRepresentative, dite_eq_right hR, Pi.zero_apply] using hx

theorem brFull_tendsto_of_agreement {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ⊤) (W : BrBoundedLp n p) (U : BrFamilyLp n p)
    (hWU : ∀ᵐ x ∂volume, ∀ R : ℝ, 1 ≤ R → brFullRepresentative W R x = brFamilyRepresentative U R x) :
    Tendsto (fun R => brFullEval R W) atTop (𝓝 (brFamilyEval inverseRadiusZero U)) := by
  apply (tendsto_brFamilyEval hpt U).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  apply Lp.ext
  filter_upwards [brFullEval_coe R W, brFamilyEval_coe (inverseRadiusAt R) U, hWU] with x hw hu hx
  exact hu.trans ((hx R hR).symm.trans hw.symm)

theorem brFull_ae_tendsto_of_agreement {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (W : BrBoundedLp n p) (U : BrFamilyLp n p) (f : BrLp n p)
    (hzero : brFamilyEval inverseRadiusZero U = f)
    (hWU : ∀ᵐ x ∂volume, ∀ R : ℝ, 1 ≤ R → brFullRepresentative W R x = brFamilyRepresentative U R x) :
    ∀ᵐ x ∂volume, Tendsto (fun R => brFullRepresentative W R x) atTop (𝓝 (f x)) := by
  have hU := brFamilyEval_coe inverseRadiusZero U
  rw [hzero] at hU
  filter_upwards [hWU, hU] with x hx hu
  rw [hu]
  apply (tendsto_brFamilyRepresentative U x).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  exact (hx R hR).symm

/-- Full positive-radius Bochner--Riesz summability on `Lᵖ`: bounded
linear realizations, the maximal estimate, and both modes of convergence. -/
theorem localSmoothing_bochnerRiesz_Lp_full_summability (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (hδ : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ W : BrLp n (ENNReal.ofReal p) →L[ℂ] BrBoundedLp n (ENNReal.ofReal p),
      ‖W‖ ≤ C ∧
      (∀ f : SchwartzMap (Space n) ℂ, ∀ᵐ x ∂volume, ∀ R : ℝ, 0 < R →
        brFullRepresentative (W (f.toLp (ENNReal.ofReal p) volume)) R x = OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x) ∧
      (∀ f : BrLp n (ENNReal.ofReal p),
        Measurable (brFullMaximal (W f)) ∧
        eLpNorm (brFullMaximal (W f)) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * ‖f‖ₑ) ∧
      (∀ f, Tendsto (fun R => brFullEval R (W f)) atTop (𝓝 f)) ∧
      (∀ f, ∀ᵐ x ∂volume, Tendsto (fun R => brFullRepresentative (W f) R x) atTop (𝓝 (f x))) := by
  obtain ⟨C, hC, W, hWnorm, hWs⟩ := localSmoothing_brBoundedLp_operator hls hn hp hδ
  obtain ⟨D, hD, U, hUnorm, hUs, hUzero⟩ := localSmoothing_brFamilyLp_operator hls hn hp hδ
  have hWU := brBounded_compact_agreement ENNReal.ofReal_ne_top
    ((le_max_left _ _).trans hδ.le) W U hWs hUs
  refine ⟨C, hC, W, hWnorm, ?_, ?_, ?_, ?_⟩
  · intro f
    filter_upwards [hWs f] with x hx
    intro R hR
    simp only [brFullRepresentative, dite_eq_left hR, hx]
    rfl
  · intro f
    refine ⟨measurable_brFullMaximal _, ?_⟩
    rw [eLpNorm_brFullMaximal]
    have H := ENNReal.ofReal_le_ofReal
      ((W.le_opNorm f).trans (mul_le_mul_of_nonneg_right hWnorm (norm_nonneg _)))
    simpa only [ENNReal.ofReal_mul hC.le, ofReal_norm] using H
  · intro f
    have H := brFull_tendsto_of_agreement ENNReal.ofReal_ne_top (W f) (U f) (hWU f)
    rw [hUzero f] at H
    exact H
  · intro f
    exact brFull_ae_tendsto_of_agreement (W f) (U f) f (hUzero f) (hWU f)

end OAI.Analysis.Fourier.BochnerRiesz
