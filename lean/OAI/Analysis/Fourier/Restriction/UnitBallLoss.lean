import OAI.Analysis.Fourier.Restriction.Sparse.Assembly
import OAI.Analysis.Fourier.Restriction.CoverPowers

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Arbitrarily small sparse-radius losses imply an arbitrarily small loss
in the number of occupied unit balls, with one uniform constant. -/
theorem unit_ball_small_loss_of_sparse {n : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {D : ℕ} (hD : 0 < D)
    (hSparse : ∀ α > (0 : ℝ), ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ SparseFourierBound n p α D C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ E : Finset (Space n), ∀ M : ℕ, 1 ≤ M → E.card ≤ M →
      ∀ f : Space n → ℂ, Measurable f → Integrable f →
        (∀ x, (∀ e ∈ E, x ∉ ball e 1) → f x = 0) →
          eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
            A * ENNReal.ofReal ((M : ℝ) ^ ε) * eLpNorm f p volume := by
  obtain ⟨N, hN, α, hα, hgap⟩ := exists_sparse_cover_loss hε D
  obtain ⟨C, hCt, hC⟩ := hSparse α hα
  let k : ℕ := (3 * D + 1) ^ N
  let A : ℝ := 3 * N * (5 * (8 : ℝ) ^ k) ^ α
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨C * ENNReal.ofReal A, ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top, ?_⟩
  intro E M hM hcard f hf hfi hfs
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : 0 < (M : ℝ) := by linarith
  have HG := sparse_cover_growth_bound hMR hα.le N k
  have HP : (M : ℝ) ^ (1 / (N : ℝ) + (k : ℝ) * α) ≤ (M : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hMR hgap.le
  calc
    _ ≤ ENNReal.ofReal (3 * N * (M : ℝ) ^ (1 / (N : ℝ))) *
        (C * ENNReal.ofReal ((5 * (4 * ((M : ℝ) + 1)) ^ k) ^ α)) * eLpNorm f p volume :=
      sparseFourierBound_unit_ball_cover hp hα.le hD hC E M N hM hcard hN hf hfi hfs
    _ = (C * ENNReal.ofReal ((3 * N * (M : ℝ) ^ (1 / (N : ℝ))) *
        (5 * (4 * ((M : ℝ) + 1)) ^ k) ^ α)) * eLpNorm f p volume := by
      have he : ENNReal.ofReal ((3 * N * (M : ℝ) ^ (1 / (N : ℝ))) *
          (5 * (4 * ((M : ℝ) + 1)) ^ k) ^ α) =
          ENNReal.ofReal (3 * N * (M : ℝ) ^ (1 / (N : ℝ))) *
            ENNReal.ofReal ((5 * (4 * ((M : ℝ) + 1)) ^ k) ^ α) :=
        ENNReal.ofReal_mul (by positivity)
      rw [he]
      ring
    _ ≤ (C * ENNReal.ofReal (A * (M : ℝ) ^ (1 / (N : ℝ) + (k : ℝ) * α))) *
        eLpNorm f p volume := by
      apply mul_le_mul _ le_rfl zero_le zero_le
      apply mul_le_mul le_rfl _ zero_le zero_le
      exact ENNReal.ofReal_le_ofReal HG
    _ ≤ (C * ENNReal.ofReal (A * (M : ℝ) ^ ε)) * eLpNorm f p volume := by
      apply mul_le_mul _ le_rfl zero_le zero_le
      apply mul_le_mul le_rfl _ zero_le zero_le
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left HP hA)
    _ = _ := by
      rw [ENNReal.ofReal_mul hA]
      ring

end OAI.Analysis.Fourier.Restriction
