import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormOperations
import OAI.RepresentationTheory.Theta.Adelic.QuadraticSquareBall

/-! # Quadratic Norm Square Classes -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareClasses

noncomputable section

/-! Squares and square cosets in the small chart of a general nonsplit
quadratic norm-one group. -/

open Set _root_.Metric
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.QuadraticNormChart
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormOperations OAI.RepresentationTheory.Theta.Adelic.QuadraticNormOperations.Small

variable {k : Type*} [NormedField k] [IsUltrametricDist k] [CharZero k]

theorem normSmall_mem_squares_iff
    (d : k) (hns : ¬ IsSquare d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1)
    (himage : QuadraticNormOperations.normSquareCoordinate d '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r))
    (a : QuadraticNormOperations.Small.normSmallSubgroup d hns r hr hr1 hdr) :
    a ∈ Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormOperations.Small.normSmallSubgroup d hns r hr hr1 hdr) ↔
      ‖QuadraticNormChart.normCoordinate d a.val‖ < ‖(2 : k)‖ * r := by
  have hsq (b : QuadraticNormOperations.Small.normSmallSubgroup d hns r hr hr1 hdr) :
      QuadraticNormChart.normCoordinate d (b.val ^ 2) = QuadraticNormOperations.normSquareCoordinate d (QuadraticNormChart.normCoordinate d b.val) := by
    obtain ⟨t, ht, he⟩ := b.property
    have hn := QuadraticNormOperations.one_add_mul_norm_eq_one d t t r hr1 hdr ht ht
    have hden : 1 + d * t ^ 2 ≠ 0 := by
      intro hz
      have he : ‖1 + d * t ^ 2‖ = 1 := by simpa only [pow_two, mul_assoc] using hn
      rw [hz, norm_zero] at he
      exact zero_ne_one he
    rw [← he, QuadraticNormChart.normCoordinate_chart, QuadraticNormOperations.normChart_sq d hns t hden, QuadraticNormChart.normCoordinate_chart]
  constructor
  · rintro ⟨b, hb⟩
    have hb' : b.val ^ 2 = a.val := congrArg Subtype.val hb
    have ht : QuadraticNormChart.normCoordinate d b.val ∈ Metric.ball (0 : k) r := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        ((QuadraticNormOperations.Small.mem_normSmallSubgroup_iff d hns r hr hr1 hdr b.val).mp b.property).2
    have he : QuadraticNormOperations.normSquareCoordinate d (QuadraticNormChart.normCoordinate d b.val) = QuadraticNormChart.normCoordinate d a.val := by
      rw [← hsq, hb']
    have hm : QuadraticNormChart.normCoordinate d a.val ∈ QuadraticNormOperations.normSquareCoordinate d '' Metric.ball 0 r := ⟨_, ht, he⟩
    rw [himage] at hm
    simpa only [Metric.mem_ball, dist_zero_right] using hm
  · intro ha
    have hm : QuadraticNormChart.normCoordinate d a.val ∈ QuadraticNormOperations.normSquareCoordinate d '' Metric.ball 0 r := by
      rw [himage]
      simpa only [Metric.mem_ball, dist_zero_right] using ha
    obtain ⟨t, ht, he⟩ := hm
    have ht' : ‖t‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using ht
    have hn := QuadraticNormOperations.one_add_mul_norm_eq_one d t t r hr1 hdr ht' ht'
    have hden : 1 + d * t ^ 2 ≠ 0 := by
      intro hz
      have he : ‖1 + d * t ^ 2‖ = 1 := by simpa only [pow_two, mul_assoc] using hn
      rw [hz, norm_zero] at he
      exact zero_ne_one he
    refine ⟨QuadraticNormOperations.Small.normSmallChart d hns r hr hr1 hdr ⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    change QuadraticNormChart.normChart d hns t ^ 2 = a.val
    rw [QuadraticNormOperations.normChart_sq d hns t hden, he]
    exact QuadraticNormChart.normChart_coordinate d hns a.val
      ((QuadraticNormOperations.Small.mem_normSmallSubgroup_iff d hns r hr hr1 hdr a.val).mp a.property).1

theorem normSmall_inverse_mul_norm
    (d : k) (hns : ¬ IsSquare d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1)
    (a b : QuadraticNormOperations.Small.normSmallSubgroup d hns r hr hr1 hdr) :
    ‖QuadraticNormChart.normCoordinate d (a⁻¹ * b).val‖ = ‖QuadraticNormChart.normCoordinate d b.val - QuadraticNormChart.normCoordinate d a.val‖ := by
  obtain ⟨t, ht, he⟩ := a.property
  obtain ⟨u, hu, he'⟩ := b.property
  have hn := QuadraticNormOperations.one_add_mul_norm_eq_one d (-t) u r hr1 hdr (by simpa only [norm_neg] using ht) hu
  have hden : 1 + d * (-t) * u ≠ 0 := by intro hz; rw [hz, norm_zero] at hn; exact zero_ne_one hn
  change ‖QuadraticNormChart.normCoordinate d (a.val⁻¹ * b.val)‖ = _
  rw [← he, ← he', QuadraticNormChart.normCoordinate_chart, QuadraticNormChart.normCoordinate_chart,
    QuadraticNormOperations.normChart_inv, QuadraticNormOperations.normChart_mul d hns (-t) u hden, QuadraticNormChart.normCoordinate_chart, norm_div, hn, div_one]
  congr 1
  ring

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareClasses
