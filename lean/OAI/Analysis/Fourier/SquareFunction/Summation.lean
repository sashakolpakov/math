import OAI.Analysis.Fourier.SquareFunction.Basic

open _root_.MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction

private theorem ennreal_rpow_iSup {ι : Sort*} (a : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, a i) ^ p = ⨆ i, a i ^ p :=
  (ENNReal.orderIsoRpow p hp).map_iSup a

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Monotone convergence for the extended `Lᵖ` norm of nonnegative functions. -/
theorem ennreal_eLpNorm_iSup {f : ℕ → X → ℝ≥0∞} (hf : ∀ j, Measurable (f j))
    (hmono : Monotone f) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x => ⨆ j, f j x) (ENNReal.ofReal p) μ =
      ⨆ j, eLpNorm (f j) (ENNReal.ofReal p) μ := by
  have hm : Measurable (fun x => ⨆ j, f j x) := Measurable.iSup hf
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity : ENNReal.ofReal p ≠ 0)
      ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, enorm_eq_self]
  simp_rw [ennreal_rpow_iSup _ hp]
  rw [lintegral_iSup (fun j => (hf j).pow_const p)
    (fun i j hij x => ENNReal.rpow_le_rpow (hmono hij x) hp.le),
    ennreal_rpow_iSup _ (one_div_pos.mpr hp)]
  congr 1
  funext j
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    (hf j).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp.le, enorm_eq_self]

/-- Infinite triangle inequality in `Lᵖ` for the nonnegative shell envelopes
used by the square-function proof. No prior finiteness is assumed. -/
theorem ennreal_eLpNorm_tsum_le {f : ℕ → X → ℝ≥0∞} (hf : ∀ j, Measurable (f j))
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => ∑' j, f j x) (ENNReal.ofReal p) μ ≤
      ∑' j, eLpNorm (f j) (ENNReal.ofReal p) μ := by
  have hp₀ : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have he : (fun x => ∑' j, f j x) =
      (fun x => ⨆ N : ℕ, ∑ j ∈ Finset.range N, f j x) := by
    funext x
    exact ENNReal.tsum_eq_iSup_nat
  rw [he, ennreal_eLpNorm_iSup]
  · apply iSup_le
    intro N
    have h := eLpNorm_sum_le (μ := μ) (f := f) (s := Finset.range N)
      (p := ENNReal.ofReal p) (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    have hs : (fun x => ∑ j ∈ Finset.range N, f j x) = ∑ j ∈ Finset.range N, f j := by
      funext x
      simp
    rw [hs]
    exact h.trans (ENNReal.sum_le_tsum (Finset.range N))
  · intro N
    exact Finset.measurable_sum _ (fun j hj => hf j)
  · intro i j hij x
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)
  · exact hp₀

theorem memLp_tsum_of_shell_bounds {f : ℕ → X → ℝ≥0∞}
    (hf : ∀ j, Measurable (f j)) {p : ℝ} (hp : 1 ≤ p)
    {B : ℕ → ℝ≥0∞} (hB : ∑' j, B j < ∞)
    (hb : ∀ j, eLpNorm (f j) (ENNReal.ofReal p) μ ≤ B j) :
    MemLp (fun x => ∑' j, f j x) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => ∑' j, f j x) (ENNReal.ofReal p) μ ≤ ∑' j, B j := by
  have h := (ennreal_eLpNorm_tsum_le hf hp).trans (ENNReal.tsum_le_tsum hb)
  exact ⟨h.trans_lt hB, h⟩

/-- The logarithmic shell losses are harmless at precisely the strict Stein
threshold. This is the infinite-synthesis step, given the individual shell
estimates; it makes no assertion that those estimates follow automatically. -/
theorem memLp_stein_shell_envelope {f : ℕ → X → ℝ≥0∞}
    (hf : ∀ j, Measurable (f j)) {n p α C A : ℝ} (hp : 1 ≤ p)
    (hα : max (1 / 2) (n * (1 / 2 - 1 / p)) < α)
    (hb : ∀ j, eLpNorm (f j) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (C * ((2 : ℝ) ^ (-(j : ℝ) *
        (α - 1 / 2 - max (n * (1 / 2 - 1 / p) - 1 / 2) 0)) *
        (1 + (j : ℝ)) ^ A))) :
    MemLp (fun x => ∑' j, f j x) (ENNReal.ofReal p) μ := by
  have hs := (summable_stein_shell_weights hα A).mul_left C
  exact (memLp_tsum_of_shell_bounds hf hp hs.tsum_ofReal_lt_top hb).1

end OAI.Analysis.Fourier.SquareFunction
