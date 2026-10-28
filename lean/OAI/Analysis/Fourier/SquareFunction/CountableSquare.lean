import OAI.Analysis.Fourier.SquareFunction.Summation
import OAI.Analysis.Fourier.SquareFunction.EnvelopeLp

/-! Passage from finite vector estimates to the square function over all
dyadic scales, without an a priori finiteness assumption. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal

theorem rpow_iSup_positive {I : Sort*} (f : I → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, f i ^ p := (ENNReal.orderIsoRpow p hp).map_iSup f

theorem ennreal_eLpNorm_iSup_directed {X I : Type*} [MeasurableSpace X] [Countable I]
    {μ : Measure X} {f : I → X → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (hd : Directed (· ≤ ·) f) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x => ⨆ i, f i x) (ENNReal.ofReal p) μ =
      ⨆ i, eLpNorm (f i) (ENNReal.ofReal p) μ := by
  have hm : Measurable (fun x => ⨆ i, f i x) := Measurable.iSup hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity)
    ENNReal.ofReal_ne_top hm.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp.le, enorm_eq_self]
  simp_rw [rpow_iSup_positive _ hp]
  rw [lintegral_iSup_directed_of_measurable (fun i => (hf i).pow_const p)]
  · rw [rpow_iSup_positive _ (one_div_pos.mpr hp)]
    congr 1
    funext i
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
      (hf i).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hp.le, enorm_eq_self]
  · intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, fun x => ENNReal.rpow_le_rpow (hik x) hp.le,
      fun x => ENNReal.rpow_le_rpow (hjk x) hp.le⟩

noncomputable def countableSquareNorm {X I H : Type*} [NormedAddCommGroup H]
    (u : I → X → H) (x : X) : ℝ≥0∞ :=
  (∑' i, ‖u i x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

theorem finite_square_eq_vectorNorm {I H : Type*} [NormedAddCommGroup H]
    (s : Finset I) (u : I → H) :
    (∑ i ∈ s, ‖u i‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (vectorNorm (fun i : s => u i)) := by
  have h : ENNReal.ofReal (vectorNorm (fun i : s => u i)) ^ (2 : ℝ) =
      ∑ i ∈ s, ‖u i‖ₑ ^ (2 : ℝ) := by
    exact (enorm_vectorNorm_sq (fun i : s => u i)).trans
      (Finset.sum_coe_sort s (fun i => ‖u i‖ₑ ^ (2 : ℝ)))
  rw [← h, ← ENNReal.rpow_mul]
  norm_num

theorem eLpNorm_countableSquareNorm {X I H : Type*} [MeasurableSpace X] [Countable I]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    {μ : Measure X} (u : I → X → H) (hu : ∀ i, Measurable (u i))
    {p : ℝ} (hp : 0 < p) :
    eLpNorm (countableSquareNorm u) (ENNReal.ofReal p) μ =
      ⨆ s : Finset I, eLpNorm (fun x => vectorNorm (fun i : s => u i x)) (ENNReal.ofReal p) μ := by
  classical
  let F : Finset I → X → ℝ≥0∞ := fun s x =>
    (∑ i ∈ s, ‖u i x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  have hF (s : Finset I) : Measurable (F s) :=
    (Finset.measurable_sum s (fun i _ => (hu i).enorm.pow_const (2 : ℝ))).pow_const _
  have hd : Directed (· ≤ ·) F := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro x
      exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset Finset.subset_union_left) (by norm_num)
    · intro x
      exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset Finset.subset_union_right) (by norm_num)
  have he : countableSquareNorm u = fun x => ⨆ s, F s x := by
    funext x
    unfold countableSquareNorm
    rw [ENNReal.tsum_eq_iSup_sum]
    exact (ENNReal.orderIsoRpow (1 / 2) (by norm_num)).map_iSup _
  rw [he, ennreal_eLpNorm_iSup_directed hF hd hp]
  congr 1
  funext s
  have hs : F s = fun x => ENNReal.ofReal (vectorNorm (fun i : s => u i x)) := by
    funext x
    exact finite_square_eq_vectorNorm s (fun i => u i x)
  rw [hs, eLpNorm_ofReal_eq μ (measurable_vectorNorm _ (fun i : s => hu i))
    (fun x => vectorNorm_nonneg _)]

theorem countableSquareNorm_bound {X I H : Type*} [MeasurableSpace X] [Countable I]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    {μ : Measure X} (u : I → X → H) (hu : ∀ i, Measurable (u i))
    {p : ℝ} (hp : 0 < p) {B : ℝ≥0∞}
    (hb : ∀ s : Finset I,
      eLpNorm (fun x => vectorNorm (fun i : s => u i x)) (ENNReal.ofReal p) μ ≤ B) :
    eLpNorm (countableSquareNorm u) (ENNReal.ofReal p) μ ≤ B := by
  rw [eLpNorm_countableSquareNorm u hu hp]
  exact iSup_le hb

end OAI.Analysis.Fourier.SquareFunction
