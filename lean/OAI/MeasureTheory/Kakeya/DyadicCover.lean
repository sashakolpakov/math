import OAI.MeasureTheory.Kakeya.LineOccupancy
import OAI.MeasureTheory.Kakeya.Maximal
import Mathlib.Analysis.SpecificLimits.Basic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

def dyadicRadius (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

theorem dyadicRadius_pos (k : ℕ) : 0 < dyadicRadius k := by unfold dyadicRadius; positivity

theorem dyadicRadius_le_one (k : ℕ) : dyadicRadius k ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

def dyadicIndices (r : ℕ → ℝ) (k : ℕ) : Set ℕ :=
  {j | dyadicRadius (k + 1) < r j ∧ r j ≤ dyadicRadius k}

def dyadicCoverSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ) (k : ℕ) : Set (Space n) :=
  ⋃ j ∈ dyadicIndices r k, Metric.ball (x j) (r j)

def dyadicExpandedSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ) (k : ℕ) : Set (Space n) :=
  ⋃ j ∈ dyadicIndices r k, Metric.ball (x j) (3 * dyadicRadius k)

theorem isOpen_dyadicCoverSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ) (k : ℕ) :
    IsOpen (dyadicCoverSet x r k) := isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball

theorem isOpen_dyadicExpandedSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ) (k : ℕ) :
    IsOpen (dyadicExpandedSet x r k) := isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball

theorem ball_subset_dyadicExpandedSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ)
    (k : ℕ) {y : Space n} (hy : y ∈ dyadicCoverSet x r k) :
    Metric.ball y (dyadicRadius k) ⊆ dyadicExpandedSet x r k := by
  obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.mp hy
  intro z hz
  apply Set.mem_iUnion₂.mpr
  refine ⟨j, hj, ?_⟩
  have hzy : dist z y < dyadicRadius k := hz
  have hyj : dist y (x j) < r j := hy
  have htriangle := dist_triangle z y (x j)
  have hrad := hj.2
  have hpos := dyadicRadius_pos k
  change dist z (x j) < 3 * dyadicRadius k
  linarith

theorem ball_union_subset_dyadicCoverSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ)
    (hr : ∀ j, r j ≤ 1) : (⋃ j, Metric.ball (x j) (r j)) ⊆ ⋃ k, dyadicCoverSet x r k := by
  intro y hy
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
  have hjpos : 0 < r j := lt_of_le_of_lt dist_nonneg (show dist y (x j) < r j from hj)
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hjpos (hr j)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion₂.mpr ⟨j, ⟨hklo, hkhi⟩, hj⟩⟩

def dyadicLineTimes {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ) (ω a : Space n) (k : ℕ) : Set ℝ :=
  Set.Icc (-(1 / 2)) (1 / 2) ∩ (fun t : ℝ ↦ a + t • ω) ⁻¹' dyadicCoverSet x r k

theorem measurableSet_dyadicLineTimes {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ)
    (ω a : Space n) (k : ℕ) : MeasurableSet (dyadicLineTimes x r ω a k) := by
  exact measurableSet_Icc.inter ((isOpen_dyadicCoverSet x r k).preimage
    (continuous_const.add (continuous_id.smul continuous_const))).measurableSet

theorem unit_line_injective {n : ℕ} {ω a : Space n} (hω : ‖ω‖ = 1) :
    Function.Injective (fun t : ℝ ↦ a + t • ω) := by
  intro t u h
  have heq : t • ω = u • ω := add_left_cancel h
  have hz : ‖(t - u) • ω‖ = 0 := by rw [sub_smul, heq, sub_self, norm_zero]
  rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_eq_zero] at hz
  exact sub_eq_zero.mp hz

theorem one_le_sum_dyadicLineTimes {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ)
    (hr : ∀ j, r j ≤ 1) {Z : Set (Space n)} (hZ : Z.Countable) {ω a : Space n}
    (hω : ‖ω‖ = 1) (hcover : OAI.MeasureTheory.Kakeya.unitSegment ω a ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j)) :
    (1 : ℝ≥0∞) ≤ ∑' k, volume (dyadicLineTimes x r ω a k) := by
  let P : Set ℝ := (fun t : ℝ ↦ a + t • ω) ⁻¹' Z
  have hP : volume P = 0 := (hZ.preimage (unit_line_injective hω)).measure_zero volume
  have hinc : Set.Icc (-(1 / 2) : ℝ) (1 / 2) ⊆ P ∪ ⋃ k, dyadicLineTimes x r ω a k := by
    intro t ht
    have hseg : a + t • ω ∈ OAI.MeasureTheory.Kakeya.unitSegment ω a := ⟨t, ht, rfl⟩
    rcases hcover hseg with hz | hb
    · exact Or.inl hz
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (ball_union_subset_dyadicCoverSet x r hr hb)
      exact Or.inr (Set.mem_iUnion.mpr ⟨k, ht, hk⟩)
  calc
    (1 : ℝ≥0∞) = volume (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) := by rw [Real.volume_Icc]; norm_num
    _ ≤ volume (P ∪ ⋃ k, dyadicLineTimes x r ω a k) := measure_mono hinc
    _ ≤ volume P + volume (⋃ k, dyadicLineTimes x r ω a k) := measure_union_le _ _
    _ ≤ volume P + ∑' k, volume (dyadicLineTimes x r ω a k) := add_le_add le_rfl (measure_iUnion_le _)
    _ = ∑' k, volume (dyadicLineTimes x r ω a k) := by rw [hP, zero_add]

theorem dyadic_occupancy_sum_lower {n : ℕ} (hn : 1 ≤ n) (x : ℕ → Space n) (r : ℕ → ℝ)
    (hr : ∀ j, r j ≤ 1) {Z : Set (Space n)} (hZ : Z.Countable) {F : Set (Space n)}
    (hF : OAI.MeasureTheory.Kakeya.IsKakeyaSet F) (hcover : F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j))
    {ω : Space n} (hω : ‖ω‖ = 1) :
    ENNReal.ofReal (lineOccupancyConstant n) ≤ ∑' k,
      OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k) ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω := by
  obtain ⟨a, ha⟩ := hF ω hω
  have hsum := one_le_sum_dyadicLineTimes x r hr hZ hω (ha.trans hcover)
  calc
    ENNReal.ofReal (lineOccupancyConstant n) = ENNReal.ofReal (lineOccupancyConstant n) * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal (lineOccupancyConstant n) * ∑' k, volume (dyadicLineTimes x r ω a k) := mul_le_mul' le_rfl hsum
    _ = ∑' k, ENNReal.ofReal (lineOccupancyConstant n) * volume (dyadicLineTimes x r ω a k) := (ENNReal.tsum_mul_left).symm
    _ ≤ ∑' k, OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k) ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω := by
      apply ENNReal.tsum_le_tsum
      intro k
      apply kakeya_indicator_ge_line_measure hn (dyadicRadius_pos k) (dyadicRadius_le_one k) hω
        (measurableSet_dyadicLineTimes x r ω a k) (fun _ h ↦ h.1)
        (isOpen_dyadicExpandedSet x r k).measurableSet
      intro t ht
      exact ball_subset_dyadicExpandedSet x r k ht.2

theorem dyadic_occupancy_integral_lower {n : ℕ} (hn : 1 ≤ n) (x : ℕ → Space n)
    (r : ℕ → ℝ) (hr : ∀ j, r j ≤ 1) {Z : Set (Space n)} (hZ : Z.Countable)
    {F : Set (Space n)} (hF : OAI.MeasureTheory.Kakeya.IsKakeyaSet F)
    (hcover : F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j)) :
    ENNReal.ofReal (lineOccupancyConstant n) * OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ≤
      ∑' k, ∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k)
        ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
  have hm (k : ℕ) : Measurable (OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k)
      ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ)))) :=
    measurable_kakeyaMaximal _ _ ((measurable_const.indicator
      (isOpen_dyadicExpandedSet x r k).measurableSet).aestronglyMeasurable)
  calc
    _ = ∫⁻ _ : Space n, ENNReal.ofReal (lineOccupancyConstant n) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
      (lintegral_const _).symm
    _ ≤ ∫⁻ ω, ∑' k, OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k)
        ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      apply lintegral_mono_ae
      filter_upwards [ae_sphereMeasure_norm n] with ω hω
      exact dyadic_occupancy_sum_lower hn x r hr hZ hF hcover hω
    _ = _ := lintegral_tsum (fun k ↦ (hm k).aemeasurable)

end OAI.MeasureTheory.Kakeya
