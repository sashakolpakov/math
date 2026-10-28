import OAI.MeasureTheory.Kakeya.Measurability

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem line_ball_times_subset_interval {n : ℕ} {δ : ℝ} {ω x y : Space n}
    (hω : ‖ω‖ = 1) :
    {t : ℝ | y ∈ Metric.ball (x + t • ω) δ} ⊆
      Set.Ioo (inner ℝ (y - x) ω - δ) (inner ℝ (y - x) ω + δ) := by
  intro t ht
  change y ∈ Metric.ball (x + t • ω) δ at ht
  have he : inner ℝ (y - (x + t • ω)) ω = inner ℝ (y - x) ω - t := by
    rw [show y - (x + t • ω) = (y - x) - t • ω by abel,
      inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hω]
    ring
  have h := abs_real_inner_le_norm (y - (x + t • ω)) ω
  rw [he, hω, mul_one] at h
  have ha : |inner ℝ (y - x) ω - t| < δ := h.trans_lt (by
    simpa only [Metric.mem_ball, dist_eq_norm] using ht)
  obtain ⟨hleft, hright⟩ := abs_lt.mp ha
  exact ⟨by linarith, by linarith⟩

/-- Thickening a measurable set of times on a unit segment occupies a
controlled amount of ambient volume. This Fubini estimate does not choose
coordinates transverse to the segment. -/
theorem line_ball_occupancy {n : ℕ} {δ : ℝ} (_hδ : 0 < δ)
    {ω x : Space n} (hω : ‖ω‖ = 1) {E : Set ℝ} (hE : MeasurableSet E)
    (hEI : E ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    {A : Set (Space n)} (hA : MeasurableSet A)
    (hthick : ∀ t ∈ E, Metric.ball (x + t • ω) δ ⊆ A) :
    volume E * volume (Metric.ball (0 : Space n) δ) ≤
      ENNReal.ofReal (2 * δ) * volume (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x) := by
  let S : Set (ℝ × Space n) :=
    {z | z.1 ∈ E ∧ z.2 ∈ Metric.ball (x + z.1 • ω) δ}
  have hS : MeasurableSet S := by
    apply (hE.preimage measurable_fst).inter
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  let F : ℝ → Space n → ℝ≥0∞ := fun t y ↦ S.indicator (fun _ ↦ 1) (t, y)
  have hF : Measurable (Function.uncurry F) := measurable_const.indicator hS
  have hfirst (t : ℝ) : (∫⁻ y, F t y) =
      E.indicator (fun _ ↦ volume (Metric.ball (0 : Space n) δ)) t := by
    by_cases ht : t ∈ E
    · have heq : F t = (Metric.ball (x + t • ω) δ).indicator (fun _ ↦ 1) := by
        funext y
        simp [F, S, Set.indicator, ht]
      rw [heq, lintegral_indicator measurableSet_ball]
      simp [ht, Measure.addHaar_ball_center]
    · have heq : F t = 0 := by funext y; simp [F, S, Set.indicator, ht]
      simp [heq, ht]
  have hsecond (y : Space n) : (∫⁻ t, F t y) ≤
      (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x).indicator (fun _ ↦ ENNReal.ofReal (2 * δ)) y := by
    by_cases hy : y ∈ A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x
    · rw [Set.indicator_of_mem hy]
      calc
        (∫⁻ t, F t y) ≤ ∫⁻ t, (Set.Ioo (inner ℝ (y - x) ω - δ)
            (inner ℝ (y - x) ω + δ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) t := by
          apply lintegral_mono
          intro t
          by_cases ht : (t, y) ∈ S
          · have hi := line_ball_times_subset_interval hω ht.2
            simp [F, ht, hi]
          · simp [F, ht]
        _ = ENNReal.ofReal (2 * δ) := by
          rw [lintegral_indicator measurableSet_Ioo]
          simp only [lintegral_const, one_mul, Measure.restrict_apply_univ,
            Real.volume_Ioo]
          congr 1
          ring
    · have heq : (fun t ↦ F t y) = 0 := by
        funext t
        have ht : (t, y) ∉ S := by
          intro ht
          exact hy ⟨hthick t ht.1 ht.2, mem_tube_iff.mpr ⟨t, hEI ht.1, ht.2⟩⟩
        simp [F, ht]
      rw [heq, Set.indicator_of_notMem hy]
      change (∫⁻ t : ℝ, (0 : ℝ≥0∞)) ≤ 0
      simp
  calc
    volume E * volume (Metric.ball (0 : Space n) δ) = ∫⁻ t, ∫⁻ y, F t y := by
      simp_rw [hfirst]
      rw [lintegral_indicator hE]
      simp [mul_comm]
    _ = ∫⁻ y, ∫⁻ t, F t y := lintegral_lintegral_swap hF.aemeasurable
    _ ≤ ∫⁻ y, (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x).indicator (fun _ ↦ ENNReal.ofReal (2 * δ)) y :=
      lintegral_mono hsecond
    _ = _ := by rw [lintegral_indicator (hA.inter (measurableSet_tube _ _ _))]; simp

def lineOccupancyConstant (n : ℕ) : ℝ := 1 / 2 ^ (n + 2)

theorem lineOccupancyConstant_pos (n : ℕ) : 0 < lineOccupancyConstant n := by
  unfold lineOccupancyConstant
  positivity

theorem scaled_occupancy_average_le {e b t a d c : ℝ≥0∞}
    (ht : t ≠ 0) (ht' : t ≠ ∞) (hd : d ≠ 0) (hd' : d ≠ ∞)
    (hocc : e * b ≤ d * a) (hscale : d * c * t ≤ b) : c * e ≤ a / t := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl ht) (Or.inl ht')).mpr
  apply (ENNReal.mul_le_mul_iff_right hd hd').mp
  calc
    d * (c * e * t) = e * (d * c * t) := by ring
    _ ≤ e * b := mul_le_mul' le_rfl hscale
    _ ≤ d * a := hocc

theorem lineOccupancyConstant_volume_bound {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) {ω : Space n} (hω : ‖ω‖ = 1)
    (x : Space n) :
    ENNReal.ofReal (2 * δ) * ENNReal.ofReal (lineOccupancyConstant n) * volume (OAI.MeasureTheory.Kakeya.tube δ ω x) ≤
      volume (Metric.ball (0 : Space n) δ) := by
  have hvol : volume (OAI.MeasureTheory.Kakeya.tube δ ω x) ≤ ENNReal.ofReal
      ((2 ^ (n + 1) * volume.real (Metric.ball (0 : Space n) 1)) * δ ^ (n - 1)) := by
    calc
      _ = ENNReal.ofReal (volume.real (OAI.MeasureTheory.Kakeya.tube δ ω x)) :=
        (ENNReal.ofReal_toReal (volume_tube_lt_top _ _ _).ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (volume_tube_real_upper hn hδ hδone hω x)
  have hpow : δ ^ n = δ ^ (n - 1) * δ := by
    simpa only [Nat.sub_add_cancel hn] using pow_succ δ (n - 1)
  have heq : (2 * δ) * lineOccupancyConstant n *
      ((2 ^ (n + 1) * volume.real (Metric.ball (0 : Space n) 1)) * δ ^ (n - 1)) =
      δ ^ n * volume.real (Metric.ball (0 : Space n) 1) := by
    unfold lineOccupancyConstant
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, hpow]
    field_simp
  calc
    _ ≤ ENNReal.ofReal (2 * δ) * ENNReal.ofReal (lineOccupancyConstant n) * ENNReal.ofReal
        ((2 ^ (n + 1) * volume.real (Metric.ball (0 : Space n) 1)) * δ ^ (n - 1)) := by gcongr
    _ = ENNReal.ofReal (δ ^ n * volume.real (Metric.ball (0 : Space n) 1)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * δ),
        ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (lineOccupancyConstant_pos n).le), heq]
    _ = volume (Metric.ball (0 : Space n) δ) := by
      rw [Measure.addHaar_ball_of_pos volume _ hδ]
      simp only [Space, finrank_euclideanSpace_fin]
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact ENNReal.ofReal_toReal measure_ball_lt_top.ne

theorem kakeya_indicator_ge_line_measure {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    {ω x : Space n} (hω : ‖ω‖ = 1) {E : Set ℝ} (hE : MeasurableSet E)
    (hEI : E ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    {A : Set (Space n)} (hA : MeasurableSet A)
    (hthick : ∀ t ∈ E, Metric.ball (x + t • ω) δ ⊆ A) :
    ENNReal.ofReal (lineOccupancyConstant n) * volume E ≤
      OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (A.indicator (fun _ ↦ (1 : ℂ))) ω := by
  have h := scaled_occupancy_average_le
    (volume_tube_pos hδ ω x).ne' (volume_tube_lt_top δ ω x).ne
    (by positivity : ENNReal.ofReal (2 * δ) ≠ 0) ENNReal.ofReal_ne_top
    (line_ball_occupancy hδ hω hE hEI hA hthick)
    (lineOccupancyConstant_volume_bound hn hδ hδone hω x)
  have hmass : (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) =
      volume (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x) := by
    have heq : (fun y ↦ ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) =
        A.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
      funext y
      by_cases hy : y ∈ A <;> simp [hy]
    rw [heq, lintegral_indicator hA]
    simp [Measure.restrict_apply hA]
  calc
    _ ≤ volume (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x) / volume (OAI.MeasureTheory.Kakeya.tube δ ω x) := h
    _ = (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω x) := by rw [hmass]
    _ ≤ _ := le_iSup (fun x : Space n ↦
      (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω x)) x

end OAI.MeasureTheory.Kakeya
