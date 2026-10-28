import OAI.Analysis.Fourier.Restriction.FourierAmplitude

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter FourierTransform
open scoped ENNReal BigOperators Topology
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem dyadic_high_monotone : Monotone (fun k : ℕ ↦ (2 : ℝ) ^ k) := by
  intro i j hij
  exact pow_le_pow_right₀ (by norm_num) hij

theorem dyadic_low_antitone : Antitone (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]

theorem amplitudeBand_dyadic_decomposition {X : Type*} (f : X → ℂ) (N : ℕ) (x : X) :
    amplitudeBand f ((1 / 2 : ℝ) ^ N) ((2 : ℝ) ^ N) x =
      (∑ k ∈ Finset.range N, amplitudeBand f ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) x) +
      ∑ k ∈ Finset.range N, amplitudeBand f ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k) x := by
  rw [sum_amplitudeBand_high f _ dyadic_high_monotone,
    sum_amplitudeBand_low f _ dyadic_low_antitone,
    amplitudeBand_eq_high_sub_high f (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 2) N)]
  simp only [pow_zero]
  ring

theorem angularFourier_amplitudeBand_dyadic {n : ℕ} {f : Space n → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (N : ℕ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f ((1 / 2 : ℝ) ^ N) ((2 : ℝ) ^ N)) ξ =
      (∑ k ∈ Finset.range N, OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) ξ) +
      ∑ k ∈ Finset.range N, OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)) ξ := by
  have he : amplitudeBand f ((1 / 2 : ℝ) ^ N) ((2 : ℝ) ^ N) =
      fun x ↦ (∑ k ∈ Finset.range N, amplitudeBand f ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) x) +
        ∑ k ∈ Finset.range N, amplitudeBand f ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k) x :=
    funext (amplitudeBand_dyadic_decomposition f N)
  rw [he, angularFourier_add]
  · rw [angularFourier_sum, angularFourier_sum]
    · intro k hk
      exact integrable_amplitudeBand hf hfi _ _
    · intro k hk
      exact integrable_amplitudeBand hf hfi _ _
  · exact integrable_finsetSum _ (fun k hk ↦ integrable_amplitudeBand hf hfi _ _)
  · exact integrable_finsetSum _ (fun k hk ↦ integrable_amplitudeBand hf hfi _ _)

theorem eLpNorm_amplitudeBand_dyadic_le {n : ℕ} {f : Space n → ℂ}
    (hf : Measurable f) (hfi : Integrable f) {q : ℝ≥0∞} (hq : 1 ≤ q) (N : ℕ) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f ((1 / 2 : ℝ) ^ N) ((2 : ℝ) ^ N))) q (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      (∑ k ∈ Finset.range N, eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))) q (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) +
      ∑ k ∈ Finset.range N, eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k))) q (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  have he := funext (angularFourier_amplitudeBand_dyadic hf hfi N)
  rw [he]
  apply (eLpNorm_add_le hq).trans
  have hs (T : ℕ → Space n → ℂ) :
      eLpNorm (fun x ↦ ∑ k ∈ Finset.range N, T k x) q (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        ∑ k ∈ Finset.range N, eLpNorm (T k) q (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    have heT : (∑ k ∈ Finset.range N, T k) = (fun x ↦ ∑ k ∈ Finset.range N, T k x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [← heT]
    exact eLpNorm_sum_le hq
  exact add_le_add (hs _) (hs _)

end OAI.Analysis.Fourier.Restriction
