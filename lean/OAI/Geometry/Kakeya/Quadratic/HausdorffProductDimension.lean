import OAI.Geometry.Kakeya.Quadratic.HausdorffProductEstimate
import OAI.Geometry.Kakeya.Quadratic.HausdorffProductGrid

open Set _root_.MeasureTheory Metric Filter
open scoped ENNReal Topology

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

omit [SecondCountableTopology X] in
theorem hausdorff_product_null {s q : ℝ} (hs : 0 < s) (hq : 0 ≤ q)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {A : Set X} {T : Set Y}
    (hT : FinitePowerCover T q C) (hTd : dimH T ≤ ENNReal.ofReal q)
    (hA : Measure.hausdorffMeasure s A = 0) :
    Measure.hausdorffMeasure (s+q) (A ×ˢ T) = 0 := by
  obtain ⟨Z, hZ, U, hc, hd, hz, hsU⟩ := hausdorff_null_positive_covers hs hA
  have hgood := hausdorff_product_null_of_positive_covers hs hq hC hT U hc hd hz hsU
  have hex : Measure.hausdorffMeasure (s+q) (Z ×ˢ T) = 0 := by
    have hlt : dimH (Z ×ˢ T) < ENNReal.ofReal (s+q) :=
      ((dimH_countable_prod hZ T).trans hTd).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
    have H := hausdorffMeasure_of_dimH_lt (d := (s+q).toNNReal) hlt
    simpa only [Real.coe_toNNReal (s+q) (by linarith : 0 ≤ s+q)] using H
  apply measure_mono_null (t := (Z ×ˢ T) ∪ ((A \ Z) ×ˢ T))
  · intro p hp
    by_cases hz : p.1 ∈ Z
    · exact Or.inl ⟨hz, hp.2⟩
    · exact Or.inr ⟨⟨hp.1, hz⟩, hp.2⟩
  · exact measure_union_null hex hgood

omit [SecondCountableTopology X] in
theorem dimH_prod_le_of_finitePowerCover {q : ℝ} (hq : 0 ≤ q)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (A : Set X) {T : Set Y}
    (hT : FinitePowerCover T q C) (hTd : dimH T ≤ ENNReal.ofReal q) :
    dimH (A ×ˢ T) ≤ dimH A + ENNReal.ofReal q := by
  by_cases hAt : dimH A = ⊤
  · simp [hAt]
  apply dimH_le
  intro d hd
  by_contra! hbad
  have hreal : (dimH A).toReal + q < (d : ℝ) := by
    have ht : dimH A + ENNReal.ofReal q ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hAt, ENNReal.ofReal_ne_top⟩
    have H := (ENNReal.toReal_lt_toReal ht ENNReal.coe_ne_top).mpr hbad
    simpa only [ENNReal.toReal_add hAt ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq, ENNReal.coe_toReal] using H
  have hs : 0 < (d : ℝ)-q := by linarith [ENNReal.toReal_nonneg (a := dimH A)]
  have hAd : dimH A < ENNReal.ofReal ((d : ℝ)-q) := by
    rw [← ENNReal.ofReal_toReal hAt, ENNReal.ofReal_lt_ofReal_iff hs]
    linarith
  have hzero : Measure.hausdorffMeasure ((d : ℝ)-q) A = 0 := by
    have H := hausdorffMeasure_of_dimH_lt (d := ((d:ℝ)-q).toNNReal) hAd
    simpa only [Real.coe_toNNReal ((d:ℝ)-q) hs.le] using H
  have H := hausdorff_product_null hs hq hC hT hTd hzero
  rw [sub_add_cancel] at H
  exact ENNReal.zero_ne_top (H.symm.trans hd)

end OAI.Geometry.Kakeya.Quadratic
