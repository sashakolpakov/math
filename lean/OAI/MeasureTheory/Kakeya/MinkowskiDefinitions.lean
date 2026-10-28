import OAI.MeasureTheory.Kakeya.Hausdorff
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-! Lower and upper Minkowski dimensions, using the standard critical
exponents of the uniform covering contents `N(r) (2r)^s` as `r ↓ 0`.
Here `N(r)` is the minimum number of closed radius-r balls with centres
in the set.  Internal and external centres give the same critical
exponents (the covering numbers differ by at most a factor-two change
of radius).  This definition retains arbitrary, not necessarily closed
or measurable, bounded sets. -/

open _root_.MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace OAI.MeasureTheory.Kakeya

def uniformCoverContent {X : Type*} [PseudoEMetricSpace X]
    (F : Set X) (s : ℝ) (r : ℝ≥0) : ℝ≥0∞ :=
  (coveringNumber r F : ℝ≥0∞) * (2 * (r : ℝ≥0∞)) ^ s

def lowerMinkowskiDimension {X : Type*} [PseudoEMetricSpace X] (F : Set X) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : liminf (uniformCoverContent F s) (𝓝[>] 0) = 0), (s : ℝ≥0∞)

def upperMinkowskiDimension {X : Type*} [PseudoEMetricSpace X] (F : Set X) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : limsup (uniformCoverContent F s) (𝓝[>] 0) = 0), (s : ℝ≥0∞)

theorem coveringNumber_ne_top_of_totallyBounded {X : Type*} [PseudoEMetricSpace X]
    {F : Set X} (hF : TotallyBounded F) {r : ℝ≥0} (hr : r ≠ 0) :
    coveringNumber r F ≠ ⊤ := by
  obtain ⟨N,hNF,hN,hcover⟩ := exists_finite_isCover_of_totallyBounded hr hF
  exact ne_top_of_le_ne_top (encard_ne_top_iff.mpr hN)
    (hcover.coveringNumber_le_encard hNF)

theorem hausdorffMeasure_le_uniformCover_liminf {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {F : Set X} (hF : TotallyBounded F)
    {s : ℝ} (hs : 0 ≤ s) :
    Measure.hausdorffMeasure s F ≤ liminf (uniformCoverContent F s) (𝓝[>] 0) := by
  classical
  let N (r : ℝ≥0) := minimalCover r F
  let (r : ℝ≥0) : Fintype (N r) := finite_minimalCover.fintype
  have hr : Tendsto (fun r : ℝ≥0 => 2 * (r : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞))
      (ENNReal.continuous_coe.tendsto (0 : ℝ≥0))
      (Or.inr (by norm_num))).mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ r : ℝ≥0 in 𝓝[>] 0, r ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ne_of_gt hr
  have hdiam : ∀ᶠ r : ℝ≥0 in 𝓝[>] 0, ∀ z : N r,
      ediam (closedBall (z : X) r) ≤ 2 * (r : ℝ≥0∞) := by
    exact Eventually.of_forall fun r z => by
      apply ediam_le
      intro x hx y hy
      have hd : dist x y ≤ 2 * (r : ℝ) := by
        calc
          dist x y ≤ dist x z + dist y z := dist_triangle_right _ _ _
          _ ≤ r + r := add_le_add hx hy
          _ = 2 * r := by ring
      simpa only [edist_dist, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hd
  have hcover : ∀ᶠ r : ℝ≥0 in 𝓝[>] 0, F ⊆ ⋃ z : N r, closedBall (z : X) r := by
    filter_upwards [hpos] with r hr
    intro x hx
    obtain ⟨z,hz,hxz⟩ := isCover_minimalCover
      (coveringNumber_ne_top_of_totallyBounded hF hr) hx
    apply mem_iUnion.mpr
    refine ⟨⟨z,hz⟩,?_⟩
    exact (ENNReal.ofReal_le_ofReal_iff r.coe_nonneg).mp (by simpa [edist_dist] using hxz)
  have h := Measure.hausdorffMeasure_le_liminf_sum s F
    (fun r : ℝ≥0 => 2 * (r : ℝ≥0∞)) hr
    (fun r (z : N r) => closedBall (z : X) r) hdiam hcover
  apply h.trans
  apply liminf_le_liminf (hv := by isBoundedDefault) (hu := by isBoundedDefault)
  filter_upwards [hpos,hdiam] with r hr hd
  calc
    ∑ z : N r, ediam (closedBall (z : X) r) ^ s ≤
        ∑ _z : N r, (2 * (r : ℝ≥0∞)) ^ s :=
      Finset.sum_le_sum fun z _ => ENNReal.rpow_le_rpow (hd z) hs
    _ = uniformCoverContent F s r := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, uniformCoverContent]
      congr 1
      have he := encard_minimalCover (coveringNumber_ne_top_of_totallyBounded hF hr)
      rw [← he]
      simp only [N, encard, ENat.card_eq_coe_fintype_card, ENat.toENNReal_coe]

theorem dimH_le_lowerMinkowskiDimension {X : Type*} [MetricSpace X]
    {F : Set X} (hF : TotallyBounded F) : dimH F ≤ lowerMinkowskiDimension F := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  apply le_iInf fun s => le_iInf fun hs => ?_
  have hz : Measure.hausdorffMeasure (s : ℝ) F = 0 :=
    le_antisymm ((hausdorffMeasure_le_uniformCover_liminf hF s.coe_nonneg).trans_eq hs) bot_le
  exact dimH_le_of_hausdorffMeasure_ne_top (by rw [hz]; exact ENNReal.zero_ne_top)

theorem lowerMinkowskiDimension_le_upper {X : Type*} [PseudoEMetricSpace X] (F : Set X) :
    lowerMinkowskiDimension F ≤ upperMinkowskiDimension F := by
  apply le_iInf fun s => le_iInf fun hs => ?_
  apply iInf₂_le s
  exact le_antisymm ((liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)).trans_eq hs) bot_le

end OAI.MeasureTheory.Kakeya
