import OAI.Analysis.Fourier.Estimates

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OAI.MeasureTheory.Kakeya

theorem isOpen_tube {n : ℕ} (δ : ℝ) (ω x : Space n) : IsOpen (OAI.MeasureTheory.Kakeya.tube δ ω x) :=
  isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball

theorem measurableSet_tube {n : ℕ} (δ : ℝ) (ω x : Space n) :
    MeasurableSet (OAI.MeasureTheory.Kakeya.tube δ ω x) := (isOpen_tube δ ω x).measurableSet

theorem mem_tube_iff {n : ℕ} {δ : ℝ} {ω x y : Space n} :
    y ∈ OAI.MeasureTheory.Kakeya.tube δ ω x ↔
      ∃ t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2), dist y (x + t • ω) < δ := by
  simp [OAI.MeasureTheory.Kakeya.tube, Metric.mem_ball]

theorem center_ball_subset_tube {n : ℕ} (δ : ℝ) (ω x : Space n) :
    Metric.ball x δ ⊆ OAI.MeasureTheory.Kakeya.tube δ ω x := by
  intro y hy
  apply mem_tube_iff.mpr
  exact ⟨0, by norm_num, by simpa using hy⟩

theorem unitSegment_subset_tube {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (ω x : Space n) :
    OAI.MeasureTheory.Kakeya.unitSegment ω x ⊆ OAI.MeasureTheory.Kakeya.tube δ ω x := by
  rintro y ⟨t, ht, rfl⟩
  exact mem_tube_iff.mpr ⟨t, ht, by simpa using hδ⟩

theorem tube_mono {n : ℕ} {δ η : ℝ} (hδη : δ ≤ η) (ω x : Space n) :
    OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ OAI.MeasureTheory.Kakeya.tube η ω x := by
  intro y hy
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  exact mem_tube_iff.mpr ⟨t, ht, hyt.trans_le hδη⟩

/-- Directions that are `η` apart move corresponding points on the centered
unit segments by at most `η/2`. -/
theorem corresponding_segment_points_close {n : ℕ} {η t : ℝ} {ω v x : Space n}
    (ht : t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2)) (hωv : dist ω v ≤ η) :
    dist (x + t • ω) (x + t • v) ≤ η / 2 := by
  rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
  have ht' : |t| ≤ 1 / 2 := abs_le.mpr ht
  have hnorm : ‖ω - v‖ ≤ η := by simpa only [dist_eq_norm] using hωv
  calc
    |t| * ‖ω - v‖ ≤ (1 / 2) * ‖ω - v‖ :=
      mul_le_mul_of_nonneg_right ht' (norm_nonneg _)
    _ ≤ (1 / 2) * η := mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = η / 2 := by ring

/-- This is the geometric inclusion used to discretize the Kakeya maximal
operator in `sections/kakeya.tex`; it holds with the sharper `3δ/2` radius. -/
theorem tube_direction_inclusion {n : ℕ} {δ η : ℝ} {ω v x : Space n}
    (hωv : dist ω v ≤ η) : OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ OAI.MeasureTheory.Kakeya.tube (δ + η / 2) v x := by
  intro y hy
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  apply mem_tube_iff.mpr
  refine ⟨t, ht, ?_⟩
  calc
    dist y (x + t • v) ≤ dist y (x + t • ω) + dist (x + t • ω) (x + t • v) :=
      dist_triangle _ _ _
    _ < δ + η / 2 := add_lt_add_of_lt_of_le hyt (corresponding_segment_points_close ht hωv)

theorem tube_direction_inclusion_double {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    {ω v x : Space n} (hωv : dist ω v ≤ δ) : OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ OAI.MeasureTheory.Kakeya.tube (2 * δ) v x :=
  (tube_direction_inclusion hωv).trans (tube_mono (by linarith) _ _)

theorem tube_subset_ball {n : ℕ} (δ : ℝ) (ω x : Space n) :
    OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ Metric.ball x (δ + ‖ω‖ / 2) := by
  intro y hy
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  have hp : dist (x + t • ω) x ≤ ‖ω‖ / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hta : |t| ≤ 1 / 2 := abs_le.mpr ht
    nlinarith [mul_le_mul_of_nonneg_right hta (norm_nonneg ω)]
  exact lt_of_le_of_lt (dist_triangle _ _ _) (add_lt_add_of_lt_of_le hyt hp)

theorem volume_tube_lt_top {n : ℕ} (δ : ℝ) (ω x : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube δ ω x) < ∞ :=
  (measure_mono (tube_subset_ball δ ω x)).trans_lt measure_ball_lt_top

theorem volume_tube_pos {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (ω x : Space n) :
    0 < volume (OAI.MeasureTheory.Kakeya.tube δ ω x) :=
  (Metric.measure_ball_pos volume x hδ).trans_le (measure_mono (center_ball_subset_tube δ ω x))

/-- If a measurable set contains a whole tube, its indicator has maximal
average at least one in that direction. -/
theorem one_le_kakeyaMaximal_indicator {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A : Set (Space n)} {ω x : Space n} (hA : OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ A) :
    1 ≤ OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (A.indicator (fun _ ↦ (1 : ℂ))) ω := by
  have hi : (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) =
      volume (OAI.MeasureTheory.Kakeya.tube δ ω x) := by
    calc
      (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) =
          ∫⁻ _y in OAI.MeasureTheory.Kakeya.tube δ ω x, (1 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_tube δ ω x)] with y hy
        simp [Set.indicator_of_mem (hA hy)]
      _ = _ := by simp
  have hq : (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) /
      volume (OAI.MeasureTheory.Kakeya.tube δ ω x) = 1 := by
    rw [hi, ENNReal.div_self (ne_of_gt (volume_tube_pos hδ ω x)) (volume_tube_lt_top δ ω x).ne]
  exact hq.symm.le.trans (le_iSup (fun x ↦
    (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω x)) x)

/-- Exact spherical cap identity underlying the packet phase estimate. -/
theorem sphere_phase_identity {n : ℕ} {ω v : Space n} (hω : ‖ω‖ = 1) (hv : ‖v‖ = 1) :
    inner ℝ v (ω - v) = -(‖ω - v‖ ^ 2) / 2 := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  have h := norm_sub_sq_real ω v
  rw [hω, hv] at h
  rw [hv]
  nlinarith [real_inner_comm ω v]

/-- Quantitative phase bound for the caps used in the restriction-to-Kakeya
randomization argument. The transverse displacement need not be orthogonal
to the direction, so this also applies to the rounded ends of the tube. -/
theorem cap_packet_phase_bound {n : ℕ} {δ c t : ℝ} {ω v z : Space n}
    (hδ : 0 < δ) (hc : 0 ≤ c) (hω : ‖ω‖ = 1) (hv : ‖v‖ = 1)
    (ht : |t| ≤ 1 / 2) (hz : ‖z‖ ≤ 2 * δ) (hcap : ‖ω - v‖ ≤ c * δ) :
    |inner ℝ (t • v + z) (ω - v) / δ ^ 2| ≤ c ^ 2 / 4 + 2 * c := by
  have hq := norm_nonneg (ω - v)
  have hq2 : ‖ω - v‖ ^ 2 ≤ (c * δ) ^ 2 := sq_le_sq₀ hq (mul_nonneg hc hδ.le) |>.mpr hcap
  have hqmul : δ * ‖ω - v‖ ≤ c * δ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcap hδ.le]
  rw [abs_div, abs_of_pos (sq_pos_of_pos hδ)]
  apply (div_le_iff₀ (sq_pos_of_pos hδ)).mpr
  calc
    |inner ℝ (t • v + z) (ω - v)| ≤
      |inner ℝ (t • v) (ω - v)| + |inner ℝ z (ω - v)| := by
        rw [inner_add_left]
        exact abs_add_le _ _
    _ = |t| * (‖ω - v‖ ^ 2 / 2) + |inner ℝ z (ω - v)| := by
      rw [real_inner_smul_left, sphere_phase_identity hω hv, abs_mul, neg_div, abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ ‖ω - v‖ ^ 2 / 2)]
    _ ≤ (1 / 2) * (‖ω - v‖ ^ 2 / 2) + (2 * δ) * ‖ω - v‖ := by
      apply add_le_add (mul_le_mul_of_nonneg_right ht (by positivity))
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hz hq)
    _ ≤ (c ^ 2 / 4 + 2 * c) * δ ^ 2 := by nlinarith

theorem cap_packet_phase_bound_small {n : ℕ} {δ t : ℝ} {ω v z : Space n}
    (hδ : 0 < δ) (hω : ‖ω‖ = 1) (hv : ‖v‖ = 1)
    (ht : |t| ≤ 1 / 2) (hz : ‖z‖ ≤ 2 * δ) (hcap : ‖ω - v‖ ≤ δ / 32) :
    |inner ℝ (t • v + z) (ω - v) / δ ^ 2| < 1 / 4 := by
  have h := cap_packet_phase_bound hδ (by norm_num : (0 : ℝ) ≤ 1 / 32)
    hω hv ht hz (by simpa only [one_div_mul_eq_div] using hcap)
  norm_num at h ⊢
  exact h.trans_lt (by norm_num)

end OAI.MeasureTheory.Kakeya
