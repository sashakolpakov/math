import OAI.Geometry.Nikodym.Definitions
import OAI.MeasureTheory.Kakeya.DyadicCover
import OAI.MeasureTheory.Kakeya.HausdorffCovers

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set
open scoped ENNReal
namespace OAI.Geometry.Nikodym

theorem unit_line_isometry {n : ℕ} {ω a : Space n} (hω : ‖ω‖ = 1) :
    Isometry (fun t : ℝ => a + t • ω) := by
  apply isometry_iff_dist_eq.mpr
  intro s t
  calc
    dist (a+s • ω) (a+t • ω) = ‖(s-t) • ω‖ := by
      rw [dist_eq_norm]
      congr 1
      module
    _ = dist s t := by rw [norm_smul,hω,mul_one]; rfl

/-- The one-dimensional Hausdorff measure in the source's segment
intersection hypothesis equals the measure of its unit-speed time set. -/
theorem hausdorffMeasure_inter_unitSegment {n : ℕ} (F : Set (Space n))
    {ω a : Space n} (hω : ‖ω‖ = 1) :
    Measure.hausdorffMeasure 1 (F ∩ OAI.MeasureTheory.Kakeya.unitSegment ω a) =
      volume (Icc (-(1/2 : ℝ)) (1/2) ∩ (fun t : ℝ => a+t • ω) ⁻¹' F) := by
  have he : (fun t : ℝ => a+t • ω) ''
      (Icc (-(1/2 : ℝ)) (1/2) ∩ (fun t : ℝ => a+t • ω) ⁻¹' F) =
      F ∩ OAI.MeasureTheory.Kakeya.unitSegment ω a := by
    ext y
    constructor
    · rintro ⟨t,⟨ht,hF⟩,rfl⟩
      exact ⟨hF,⟨t,ht,rfl⟩⟩
    · rintro ⟨hF,t,ht,rfl⟩
      exact ⟨t,⟨ht,hF⟩,rfl⟩
  rw [← he,(unit_line_isometry hω).hausdorffMeasure_image (Or.inl (by norm_num)),
    hausdorffMeasure_real]

theorem line_intersection_le_sum_dyadicLineTimes {n : ℕ}
    (x : ℕ → Space n) (r : ℕ → ℝ) (hr : ∀ j, r j ≤ 1)
    {Z F : Set (Space n)} (hZ : Z.Countable) {ω a : Space n} (hω : ‖ω‖ = 1)
    (hcover : F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j)) :
    Measure.hausdorffMeasure 1 (F ∩ OAI.MeasureTheory.Kakeya.unitSegment ω a) ≤
      ∑' k, volume (OAI.MeasureTheory.Kakeya.dyadicLineTimes x r ω a k) := by
  rw [hausdorffMeasure_inter_unitSegment F hω]
  let P : Set ℝ := (fun t : ℝ => a+t • ω) ⁻¹' Z
  have hP : volume P = 0 := (hZ.preimage (OAI.MeasureTheory.Kakeya.unit_line_injective hω)).measure_zero volume
  have hinc : Icc (-(1/2 : ℝ)) (1/2) ∩ (fun t : ℝ => a+t • ω) ⁻¹' F ⊆
      P ∪ ⋃ k, OAI.MeasureTheory.Kakeya.dyadicLineTimes x r ω a k := by
    intro t ht
    rcases hcover ht.2 with hz | hb
    · exact Or.inl hz
    · obtain ⟨k,hk⟩ := mem_iUnion.mp (OAI.MeasureTheory.Kakeya.ball_union_subset_dyadicCoverSet x r hr hb)
      exact Or.inr (mem_iUnion.mpr ⟨k,ht.1,hk⟩)
  calc
    _ ≤ volume (P ∪ ⋃ k,OAI.MeasureTheory.Kakeya.dyadicLineTimes x r ω a k) := measure_mono hinc
    _ ≤ volume P + volume (⋃ k,OAI.MeasureTheory.Kakeya.dyadicLineTimes x r ω a k) := measure_union_le _ _
    _ ≤ volume P + ∑' k,volume (OAI.MeasureTheory.Kakeya.dyadicLineTimes x r ω a k) :=
      add_le_add le_rfl (measure_iUnion_le _)
    _ = _ := by rw [hP,zero_add]

theorem nikodym_indicator_ge_line_measure {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    {ω a x : Space n} (hω : ‖ω‖ = 1) (hx : x ∈ OAI.MeasureTheory.Kakeya.unitSegment ω a)
    {E : Set ℝ} (hE : MeasurableSet E) (hEI : E ⊆ Icc (-(1/2 : ℝ)) (1/2))
    {A : Set (Space n)} (hA : MeasurableSet A)
    (hthick : ∀ t ∈ E, Metric.ball (a+t • ω) δ ⊆ A) :
    ENNReal.ofReal (OAI.MeasureTheory.Kakeya.lineOccupancyConstant n) * volume E ≤
      nikodymMaximal δ (A.indicator (fun _ => (1:ℂ))) x := by
  have h := OAI.MeasureTheory.Kakeya.scaled_occupancy_average_le
    (OAI.MeasureTheory.Kakeya.volume_tube_pos hδ ω a).ne' (OAI.MeasureTheory.Kakeya.volume_tube_lt_top δ ω a).ne
    (by positivity : ENNReal.ofReal (2*δ) ≠ 0) ENNReal.ofReal_ne_top
    (OAI.MeasureTheory.Kakeya.line_ball_occupancy hδ hω hE hEI hA hthick)
    (OAI.MeasureTheory.Kakeya.lineOccupancyConstant_volume_bound hn hδ hδone hω a)
  have hmass : (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω a, ‖A.indicator (fun _ => (1:ℂ)) y‖ₑ) =
      volume (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω a) := by
    have he : (fun y => ‖A.indicator (fun _ => (1:ℂ)) y‖ₑ) =
        A.indicator (fun _ => (1:ℝ≥0∞)) := by
      funext y
      by_cases hy : y ∈ A <;> simp [hy]
    rw [he,lintegral_indicator hA]
    simp [Measure.restrict_apply hA]
  calc
    _ ≤ volume (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω a) / volume (OAI.MeasureTheory.Kakeya.tube δ ω a) := h
    _ = (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω a, ‖A.indicator (fun _ => (1:ℂ)) y‖ₑ) /
        volume (OAI.MeasureTheory.Kakeya.tube δ ω a) := by rw [hmass]
    _ ≤ _ := tube_average_le_nikodymMaximal _ hω hx

/-- A source-form Nikodym incidence hypothesis, using positive Hausdorff
length along a unit segment through each point, not full contained lines. -/
def HasNikodymSegments {n : ℕ} (F Ω : Set (Space n)) (ell : ℝ) : Prop :=
  ∀ x ∈ Ω, ∃ ω a : Space n, ‖ω‖ = 1 ∧ x ∈ OAI.MeasureTheory.Kakeya.unitSegment ω a ∧
    ENNReal.ofReal ell ≤ Measure.hausdorffMeasure 1 (F ∩ OAI.MeasureTheory.Kakeya.unitSegment ω a)

theorem nikodym_dyadic_occupancy_sum_lower {n : ℕ} (hn : 1 ≤ n)
    (x : ℕ → Space n) (r : ℕ → ℝ) (hr : ∀ j, r j ≤ 1)
    {Z F Ω : Set (Space n)} (hZ : Z.Countable) {ell : ℝ}
    (hF : HasNikodymSegments F Ω ell)
    (hcover : F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j))
    {y : Space n} (hy : y ∈ Ω) :
    ENNReal.ofReal (OAI.MeasureTheory.Kakeya.lineOccupancyConstant n) * ENNReal.ofReal ell ≤
      ∑' k,nikodymMaximal (OAI.MeasureTheory.Kakeya.dyadicRadius k)
        ((OAI.MeasureTheory.Kakeya.dyadicExpandedSet x r k).indicator (fun _ => (1:ℂ))) y := by
  obtain ⟨ω,a,hω,hya,hell⟩ := hF y hy
  have hsum := hell.trans (line_intersection_le_sum_dyadicLineTimes x r hr hZ hω hcover)
  calc
    _ ≤ ENNReal.ofReal (OAI.MeasureTheory.Kakeya.lineOccupancyConstant n) *
        ∑' k,volume (OAI.MeasureTheory.Kakeya.dyadicLineTimes x r ω a k) := mul_le_mul' le_rfl hsum
    _ = ∑' k,ENNReal.ofReal (OAI.MeasureTheory.Kakeya.lineOccupancyConstant n) *
        volume (OAI.MeasureTheory.Kakeya.dyadicLineTimes x r ω a k) := (ENNReal.tsum_mul_left).symm
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro k
      apply nikodym_indicator_ge_line_measure hn (OAI.MeasureTheory.Kakeya.dyadicRadius_pos k) (OAI.MeasureTheory.Kakeya.dyadicRadius_le_one k)
        hω hya (OAI.MeasureTheory.Kakeya.measurableSet_dyadicLineTimes x r ω a k) (fun _ ht => ht.1)
        (OAI.MeasureTheory.Kakeya.isOpen_dyadicExpandedSet x r k).measurableSet
      intro t ht
      exact OAI.MeasureTheory.Kakeya.ball_subset_dyadicExpandedSet x r k ht.2

end OAI.Geometry.Nikodym
