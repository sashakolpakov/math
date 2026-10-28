import OAI.Analysis.Fourier.Estimates
import Mathlib.MeasureTheory.Measure.Hausdorff

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Metric
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem nonempty_ediam_rpow {E : Type*} [EMetricSpace E] {s : ℝ} (hs : 0 < s) (T : Set E) :
    (⨆ _ : T.Nonempty, ediam T ^ s) = ediam T ^ s := by
  by_cases hT : T.Nonempty
  · simp [hT]
  · simp [Set.not_nonempty_iff_eq_empty.mp hT, hs]

theorem hausdorff_null_small_set_cover {E : Type*} [EMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] {s : ℝ} (hs : 0 < s) {F : Set E}
    (hF : Measure.hausdorffMeasure s F = 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ T : ℕ → Set E, F ⊆ ⋃ j, T j ∧ (∀ j, ediam (T j) ≤ (1 / 2 : ℝ≥0∞)) ∧
      (∑' j, ediam (T j) ^ s) < ε := by
  have hbound : (⨅ (T : ℕ → Set E) (_ : F ⊆ ⋃ j, T j)
      (_ : ∀ j, ediam (T j) ≤ (1 / 2 : ℝ≥0∞)), ∑' j, ⨆ _ : (T j).Nonempty, ediam (T j) ^ s) ≤
      Measure.hausdorffMeasure s F := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le (1 / 2 : ℝ≥0∞)
      (le_iSup_of_le (by norm_num : (0 : ℝ≥0∞) < 1 / 2) le_rfl)
  have hlt := hbound.trans_lt (hF ▸ hε)
  obtain ⟨T, hcover, hdiam, hcost⟩ := (by simpa only [iInf_lt_iff] using hlt)
  refine ⟨T, hcover, hdiam, ?_⟩
  simpa only [nonempty_ediam_rpow hs] using hcost

/-- Zero Hausdorff measure supplies arbitrarily cheap ball covers, apart
from a countable set. Zero-diameter covering sets are retained as that
countable exception, so no positive-radius padding argument is needed. -/
theorem hausdorff_null_ball_cover {n : ℕ} {s : ℝ} (hs : 0 < s) {F : Set (Space n)}
    (hF : Measure.hausdorffMeasure s F = 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (x : ℕ → Space n) (r : ℕ → ℝ) (Z : Set (Space n)),
      Z.Countable ∧ F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j) ∧
      (∀ j, 0 ≤ r j ∧ r j ≤ 1) ∧
      (∑' j, ENNReal.ofReal (r j) ^ s) ≤ (2 : ℝ≥0∞) ^ s * ε := by
  classical
  obtain ⟨T, hcover, hdiam, hcost⟩ := hausdorff_null_small_set_cover hs hF hε
  have hfin (j : ℕ) : ediam (T j) ≠ ∞ := ne_top_of_le_ne_top (by norm_num) (hdiam j)
  let x : ℕ → Space n := fun j ↦ if h : (T j).Nonempty then h.choose else 0
  let r : ℕ → ℝ := fun j ↦ 2 * (ediam (T j)).toReal
  let Z : Set (Space n) := ⋃ j, if ediam (T j) = 0 then T j else ∅
  have hZ : Z.Countable := by
    apply Set.countable_iUnion
    intro j
    by_cases hj : ediam (T j) = 0
    · simpa only [ite_eq_left hj] using (ediam_eq_zero_iff.mp hj).countable
    · simp [hj]
  refine ⟨x, r, Z, hZ, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover hy)
    by_cases hzero : ediam (T j) = 0
    · left
      exact Set.mem_iUnion.mpr ⟨j, by simpa [hzero] using hj⟩
    · right
      have hT : (T j).Nonempty := ⟨y, hj⟩
      have hx : x j ∈ T j := by simpa only [x, dite_eq_left hT] using hT.choose_spec
      have hdpos : 0 < (ediam (T j)).toReal := ENNReal.toReal_pos hzero (hfin j)
      have hd := ENNReal.toReal_mono (hfin j) (edist_le_ediam_of_mem hj hx)
      have hdist : dist y (x j) ≤ (ediam (T j)).toReal := by
        simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using hd
      exact Set.mem_iUnion.mpr ⟨j, by change dist y (x j) < 2 * (ediam (T j)).toReal; linarith⟩
  · intro j
    have h := ENNReal.toReal_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞) (hdiam j)
    norm_num at h
    exact ⟨by positivity, by dsimp [r]; linarith⟩
  · have heq (j : ℕ) : ENNReal.ofReal (r j) ^ s = (2 : ℝ≥0∞) ^ s * ediam (T j) ^ s := by
      dsimp only [r]
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_toReal (hfin j), ENNReal.mul_rpow_of_nonneg _ _ hs.le]
    simp_rw [heq]
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul' le_rfl hcost.le

end OAI.MeasureTheory.Kakeya
