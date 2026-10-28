import OAI.Geometry.Kakeya.Quadratic.HausdorffProductCover

open Set _root_.MeasureTheory Metric Filter
open scoped ENNReal Topology

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

omit [SecondCountableTopology X] in
/-- A sharp product-cover estimate.  Both factors use their actual metric;
the cover exponent will be supplied by explicit Euclidean grids. -/
theorem hausdorff_product_null_of_positive_covers
    {s q : ℝ} (hs : 0 < s) (hq : 0 ≤ q)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {A : Set X} {T : Set Y}
    (hT : FinitePowerCover T q C) (U : ℕ → ℕ → Set X)
    (hcov : ∀ n, A ⊆ ⋃ j, U n j)
    (hd : ∀ n j, ediam (U n j) ≤ (1/2 : ℝ≥0∞)^n)
    (hz : ∀ n j, ediam (U n j) = 0 → U n j = ∅)
    (hc : ∀ n, (∑' j, ediam (U n j)^s) ≤ (1/2 : ℝ≥0∞)^n) :
    Measure.hausdorffMeasure (s+q) (A ×ˢ T) = 0 := by
  classical
  let J (n : ℕ) := {j : ℕ // 0 < ediam (U n j)}
  have hone (n : ℕ) : (1/2 : ℝ≥0∞)^n ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
  choose N V hVc hVd hVcost using fun (n : ℕ) (j : J n) =>
    hT (ediam (U n j.val)) j.property ((hd n j.val).trans (hone n))
  let I (n : ℕ) := Σ j : J n, Fin (N n j)
  let W (n : ℕ) (i : I n) : Set (X × Y) := U n i.1.val ×ˢ V n i.1 i.2
  have hWd (n : ℕ) (i : I n) : ediam (W n i) ≤ (1/2 : ℝ≥0∞)^n :=
    (ediam_prod_le le_rfl (hVd n i.1 i.2)).trans (hd n i.1.val)
  have hWc (n : ℕ) : A ×ˢ T ⊆ ⋃ i : I n, W n i := by
    intro p hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov n hp.1)
    have hjp : 0 < ediam (U n j) := by
      by_contra! hh
      have hzero : ediam (U n j) = 0 := le_antisymm hh bot_le
      simp [hz n j hzero] at hj
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hVc n ⟨j, hjp⟩ hp.2)
    exact mem_iUnion.mpr ⟨⟨⟨j, hjp⟩, i⟩, hj, hi⟩
  have hsum (n : ℕ) : (∑' i : I n, ediam (W n i)^(s+q)) ≤ C*(1/2 : ℝ≥0∞)^n := by
    calc
      (∑' i : I n, ediam (W n i)^(s+q)) ≤
          ∑' i : I n, ediam (U n i.1.val)^(s+q) :=
        ENNReal.tsum_le_tsum fun i => ENNReal.rpow_le_rpow
          (ediam_prod_le le_rfl (hVd n i.1 i.2)) (by linarith)
      _ = ∑' j : J n, (N n j : ℝ≥0∞)*ediam (U n j.val)^(s+q) := by
        rw [ENNReal.tsum_sigma']
        congr 1
        ext j
        simp
      _ ≤ ∑' j : J n, C*ediam (U n j.val)^s := by
        apply ENNReal.tsum_le_tsum
        intro j
        have hjt : ediam (U n j.val) ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) (hd n j.val)
        rw [ENNReal.rpow_add _ _ j.property.ne' hjt]
        calc
          (N n j : ℝ≥0∞) * (ediam (U n j.val)^s * ediam (U n j.val)^q) =
              ((N n j : ℝ≥0∞)*ediam (U n j.val)^q)*ediam (U n j.val)^s := by ac_rfl
          _ ≤ C*ediam (U n j.val)^s := mul_le_mul' (hVcost n j) le_rfl
      _ = C * ∑' j : J n, ediam (U n j.val)^s := by rw [ENNReal.tsum_mul_left]
      _ ≤ C * ∑' j : ℕ, ediam (U n j)^s := by
        apply mul_le_mul' le_rfl
        exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
          (fun j : ℕ => ediam (U n j)^s)
      _ ≤ C*(1/2 : ℝ≥0∞)^n := mul_le_mul' le_rfl (hc n)
  have hlim : Tendsto (fun n : ℕ => (1/2 : ℝ≥0∞)^n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hClim : Tendsto (fun n : ℕ => C*(1/2 : ℝ≥0∞)^n) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr hC)
  apply le_antisymm _ bot_le
  calc
    Measure.hausdorffMeasure (s+q) (A ×ˢ T) ≤
        liminf (fun n => ∑' i : I n, ediam (W n i)^(s+q)) atTop :=
      Measure.hausdorffMeasure_le_liminf_tsum (s+q) (A ×ˢ T) _ hlim W
        (Eventually.of_forall hWd) (Eventually.of_forall hWc)
    _ ≤ liminf (fun n : ℕ => C*(1/2 : ℝ≥0∞)^n) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall hsum)
    _ = 0 := hClim.liminf_eq

end OAI.Geometry.Kakeya.Quadratic
