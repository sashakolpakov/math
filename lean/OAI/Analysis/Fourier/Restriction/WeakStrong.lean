import OAI.Analysis.Fourier.SquareFunction.Maximal

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- A weak power bound plus a uniform bound gives every strictly higher
strong moment, on an arbitrary measure space. -/
theorem lintegral_power_le_of_weak_and_bounded
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {u : X → ℝ} (hu : Measurable u) (hun : ∀ x, 0 ≤ u x)
    {L b q : ℝ} (hL : 0 ≤ L) (hub : ∀ x, u x ≤ L)
    (hb : 0 < b) (hqb : q < b) {A : ℝ≥0∞}
    (hweak : ∀ t > 0, μ {x | t < u x} ≤ A * ENNReal.ofReal (t ^ (-q))) :
    (∫⁻ x, ENNReal.ofReal (u x) ^ b ∂μ) ≤
      A * ENNReal.ofReal (b * (L ^ (b - q) / (b - q))) := by
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), μ {x | t < u x} *
        ENNReal.ofReal b * ENNReal.ofReal t ^ (b - 1) :=
      OAI.Analysis.Fourier.SquareFunction.lintegral_power_layercake μ hu hun hb
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (Iio L).indicator
        (fun t ↦ (A * ENNReal.ofReal b) * ENNReal.ofReal t ^ (b - q - 1)) t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      by_cases htL : t < L
      · rw [Set.indicator_of_mem (show t ∈ Iio L from htL)]
        calc
          _ ≤ (A * ENNReal.ofReal (t ^ (-q))) * ENNReal.ofReal b * ENNReal.ofReal t ^ (b - 1) := by
            gcongr
            exact hweak t ht
          _ = _ := by
            rw [← ENNReal.ofReal_rpow_of_pos ht]
            have he : ENNReal.ofReal t ^ (-q) * ENNReal.ofReal t ^ (b - 1) =
                ENNReal.ofReal t ^ (b - q - 1) := by
              rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top]
              congr 1
              ring
            calc
              _ = (A * ENNReal.ofReal b) *
                  (ENNReal.ofReal t ^ (-q) * ENNReal.ofReal t ^ (b - 1)) := by ring
              _ = _ := by rw [he]
      · have hempty : {x | t < u x} = ∅ := by
          ext x
          simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun hx ↦ htL (hx.trans_le (hub x))
        rw [Set.indicator_of_notMem (show t ∉ Iio L from htL), hempty,
          measure_empty, zero_mul, zero_mul]
    _ = (A * ENNReal.ofReal b) *
        ENNReal.ofReal (L ^ (b - q) / (b - q)) := by
      rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
      have he : Iio L ∩ Ioi (0 : ℝ) = Ioo 0 L := by
        ext t
        simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
        tauto
      have hm : Measurable (fun t : ℝ ↦ ENNReal.ofReal t ^ (b - q - 1)) := by fun_prop
      rw [he, lintegral_const_mul _ hm,
        OAI.Analysis.Fourier.SquareFunction.lintegral_power_Ioo hL (by linarith : -1 < b - q - 1)]
      simp only [sub_add_cancel]
    _ = _ := by
      rw [mul_assoc, ← ENNReal.ofReal_mul hb.le]

end OAI.Analysis.Fourier.Restriction
