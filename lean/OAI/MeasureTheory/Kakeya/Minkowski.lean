import OAI.MeasureTheory.Kakeya.MinkowskiCover

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem uniformCoverContent_tendsto_zero_of_dim_lt {n : ℕ} {F : Set (Space n)}
    (hF : Bornology.IsBounded F) {s : ℝ} (hs : (n : ℝ) < s) :
    Tendsto (uniformCoverContent F s) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := bounded_coveringNumber_power_bound hF
  have hs0 : 0 ≤ s := (Nat.cast_nonneg n).trans hs.le
  have hpow : (2 : ℝ≥0∞) ^ s ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg hs0 (by norm_num)).ne
  have hlim : Tendsto (fun r : ℝ≥0 => (C * 2 ^ s) * (r : ℝ≥0∞) ^ (s - n))
      (𝓝[>] 0) (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos (ENNReal.mul_ne_top hC hpow)
      (sub_pos.mpr hs)).comp (ENNReal.continuous_coe.tendsto (0 : ℝ≥0) |>.mono_left nhdsWithin_le_nhds)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le)
  have hr1 : ∀ᶠ r : ℝ≥0 in 𝓝[>] 0, r < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ≥0) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hr1] with r hr hr1
  have hr0 : (r : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hr)
  have he : (r : ℝ≥0∞) ^ s = (r : ℝ≥0∞) ^ n * (r : ℝ≥0∞) ^ (s - n) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ hr0 ENNReal.coe_ne_top]
    congr 1
    ring
  calc
    uniformCoverContent F s r =
        ((coveringNumber r F : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) * (2 ^ s * (r : ℝ≥0∞) ^ (s - n)) := by
      rw [uniformCoverContent, ENNReal.mul_rpow_of_nonneg _ _ hs0, he]
      ring
    _ ≤ C * (2 ^ s * (r : ℝ≥0∞) ^ (s - n)) := mul_le_mul' (hbound r hr hr1.le) le_rfl
    _ = (C * 2 ^ s) * (r : ℝ≥0∞) ^ (s - n) := by rw [mul_assoc]

theorem upperMinkowskiDimension_le_dimension {n : ℕ} {F : Set (Space n)}
    (hF : Bornology.IsBounded F) : upperMinkowskiDimension F ≤ n := by
  by_contra h
  obtain ⟨s,hns,hsM⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge h)
  have hns' : (n : ℝ) < s := by exact_mod_cast hns
  have hlim := (uniformCoverContent_tendsto_zero_of_dim_lt hF hns').limsup_eq
  have hle : upperMinkowskiDimension F ≤ s := iInf₂_le s hlim
  exact hsM.not_ge hle

/-- The usual dimension comparison for every bounded Euclidean set. -/
theorem bounded_minkowski_dimension_comparison {n : ℕ} {F : Set (Space n)}
    (hF : Bornology.IsBounded F) :
    dimH F ≤ lowerMinkowskiDimension F ∧
      lowerMinkowskiDimension F ≤ upperMinkowskiDimension F ∧
      upperMinkowskiDimension F ≤ n := by
  have htot : TotallyBounded F :=
    (isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure,hF.closure⟩).totallyBounded.subset subset_closure
  exact ⟨dimH_le_lowerMinkowskiDimension htot,
    lowerMinkowskiDimension_le_upper F, upperMinkowskiDimension_le_dimension hF⟩

/-- Every bounded set with full Hausdorff dimension has both full
Minkowski dimensions; no closedness or measurability is needed. -/
theorem minkowski_dimensions_eq_of_dimH_eq {n : ℕ} {F : Set (Space n)}
    (hF : Bornology.IsBounded F) (hd : dimH F = n) :
    lowerMinkowskiDimension F = n ∧ upperMinkowskiDimension F = n := by
  obtain ⟨h1,h2,h3⟩ := bounded_minkowski_dimension_comparison hF
  rw [hd] at h1
  exact ⟨le_antisymm (h2.trans h3) h1, le_antisymm h3 (h1.trans h2)⟩

/-- The bounded-set clause of `cor:kakeya-dimension`, including both
lower and upper Minkowski dimensions. -/
theorem kakeyaMaximal_implies_minkowski_dimensions (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {n : ℕ} (hn : 2 ≤ n) {F : Set (Space n)}
    (hF : OAI.MeasureTheory.Kakeya.IsKakeyaSet F) (hbounded : Bornology.IsBounded F) :
    lowerMinkowskiDimension F = n ∧ upperMinkowskiDimension F = n :=
  minkowski_dimensions_eq_of_dimH_eq hbounded (kakeyaMaximal_implies_kakeya hK n hn F hF)

/-- The same source clause requires only the Hausdorff-dimensional
Kakeya theorem, allowing direct use of the unconditional public result. -/
theorem kakeya_implies_minkowski_dimensions (hK : OAI.MeasureTheory.Kakeya.KakeyaConjecture)
    {n : ℕ} (hn : 2 ≤ n) {F : Set (Space n)}
    (hF : OAI.MeasureTheory.Kakeya.IsKakeyaSet F) (hbounded : Bornology.IsBounded F) :
    lowerMinkowskiDimension F = n ∧ upperMinkowskiDimension F = n :=
  minkowski_dimensions_eq_of_dimH_eq hbounded (hK n hn F hF)

end OAI.MeasureTheory.Kakeya
