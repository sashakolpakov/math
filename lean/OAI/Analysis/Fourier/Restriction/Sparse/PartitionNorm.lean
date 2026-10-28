import OAI.Analysis.Fourier.Restriction.Sparse.Partition
import OAI.Analysis.Fourier.Restriction.Sparse.PieceNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem finite_rpow_bound {N : ℕ} (a b : Fin N → ℝ≥0∞) (D : ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) (h : ∀ i, a i ≤ D * b i) :
    (∑ i, a i ^ p) ^ (1 / p) ≤ D * (∑ i, b i ^ p) ^ (1 / p) := by
  calc
    _ ≤ (∑ i, (D * b i) ^ p) ^ (1 / p) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      exact Finset.sum_le_sum (fun i _ ↦ ENNReal.rpow_le_rpow (h i) hp.le)
    _ = (D ^ p * ∑ i, b i ^ p) ^ (1 / p) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      rw [Finset.mul_sum]
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        mul_one_div_cancel hp.ne', ENNReal.rpow_one]

theorem disjoint_indicator_Lp_sum_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {N : ℕ} (s : Fin N → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j ↦ Disjoint (s i) (s j)))
    {f : X → ℂ} (hf : Measurable f) {p : ℝ} (hp : 0 < p) :
    (∑ i, eLpNorm ((s i).indicator f) (ENNReal.ofReal p) μ ^ p) ^ (1 / p) ≤
      eLpNorm f (ENNReal.ofReal p) μ := by
  have hi (i : Fin N) : eLpNorm ((s i).indicator f) (ENNReal.ofReal p) μ ^ p =
      ∫⁻ x, ‖(s i).indicator f x‖ₑ ^ p ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
      (hf.indicator (hs i)).aestronglyMeasurable, ENNReal.toReal_ofReal hp.le,
      ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  simp_rw [hi]
  rw [← MeasureTheory.lintegral_finsetSum _ (fun i _ ↦ (hf.indicator (hs i)).enorm.pow_const p),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
      hf.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  exact lintegral_mono (sum_indicator_enorm_rpow_le s hd f hp)

theorem sparsePiece_Lp_sum_le {n N : ℕ} (u : SchwartzMap (Space n) ℂ)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) (hu : ∀ x, ‖x‖ ≤ 1 → c ≤ ‖u x‖)
    (z : Fin N → Space n)
    (hd : Pairwise (fun i j ↦ Disjoint (ball (z i) R) (ball (z j) R)))
    {f : Space n → ℂ} (hf : Measurable f) {p : ℝ} (hp : 0 < p) :
    (∑ i, eLpNorm (sparsePiece u R (z i) f) (ENNReal.ofReal p) volume ^ p) ^ (1 / p) ≤
      ENNReal.ofReal c⁻¹ * eLpNorm f (ENNReal.ofReal p) volume := by
  apply (finite_rpow_bound _ _ (ENNReal.ofReal c⁻¹) hp
    (fun i ↦ eLpNorm_sparsePiece_le u hc hR hu (z i) hf _)).trans
  exact mul_le_mul' le_rfl (disjoint_indicator_Lp_sum_le volume (fun i ↦ ball (z i) R)
    (fun _ ↦ measurableSet_ball) hd hf hp)

end OAI.Analysis.Fourier.Restriction
