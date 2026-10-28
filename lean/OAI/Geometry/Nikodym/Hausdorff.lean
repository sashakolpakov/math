import OAI.Geometry.Nikodym.HausdorffCover
import OAI.MeasureTheory.Kakeya.Hausdorff

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OAI.Geometry.Nikodym

/-- Nikodym maximal estimates force positive Hausdorff measure in every
strictly subcritical dimension, for positive-length incidences through a
positive finite-measure set of points. -/
theorem nikodym_hausdorffMeasure_ne_zero_finite (hN : NikodymMaximalConjecture)
    {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hsn : s < n)
    {F Ω : Set (Space n)} (hΩ : MeasurableSet Ω)
    (hΩpos : 0 < volume Ω) (hΩfin : volume Ω < ∞)
    {ell : ℝ} (hell : 0 < ell) (hF : HasNikodymSegments F Ω ell) :
    Measure.hausdorffMeasure s F ≠ 0 := by
  intro hnull
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < 1/(n:ℝ) := by positivity
  obtain ⟨D,hD,hbound⟩ := nikodym_maximal_implies_cover_sum_bound hN hn hs hsn Ω hΩfin
  let A : ℝ≥0∞ := (2:ℝ≥0∞)^s
  have hA : A < ∞ := ENNReal.rpow_lt_top_of_nonneg hs.le (by norm_num)
  have hsmall (j : ℕ) :
      (ENNReal.ofReal (OAI.MeasureTheory.Kakeya.lineOccupancyConstant n) * ENNReal.ofReal ell) * volume Ω ≤
        D * (A * (1/2 : ℝ≥0∞)^j)^(1/(n:ℝ)) := by
    have hε : 0 < (1/2 : ℝ≥0∞)^j := pos_iff_ne_zero.mpr (pow_ne_zero j (by norm_num))
    obtain ⟨x,r,Z,hZ,hcover,hr,hcost⟩ := OAI.MeasureTheory.Kakeya.hausdorff_null_ball_cover hs hnull hε
    have hcostfin : OAI.MeasureTheory.Kakeya.ballCoverCost s r < ∞ :=
      lt_of_le_of_lt hcost (ENNReal.mul_lt_top hA (by finiteness))
    have hlo := nikodym_dyadic_occupancy_integral_lower (show 1 ≤ n by omega)
      x r (fun j => (hr j).2) hZ hΩ hF hcover
    exact hlo.trans ((hbound x r hcostfin).trans
      (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hcost hq.le)))
  have hgeo : Tendsto (fun j : ℕ => (1/2 : ℝ≥0∞)^j) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have harg : Tendsto (fun j : ℕ => A * (1/2 : ℝ≥0∞)^j) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hgeo (Or.inr hA.ne)
  have hlim : Tendsto (fun j : ℕ => D * (A * (1/2 : ℝ≥0∞)^j)^(1/(n:ℝ)))
      atTop (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hD.ne hq).comp harg
  have hzero : (ENNReal.ofReal (OAI.MeasureTheory.Kakeya.lineOccupancyConstant n) * ENNReal.ofReal ell) * volume Ω ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall hsmall)
  have hpositive : 0 < (ENNReal.ofReal (OAI.MeasureTheory.Kakeya.lineOccupancyConstant n) * ENNReal.ofReal ell) * volume Ω :=
    ENNReal.mul_pos
      (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (OAI.MeasureTheory.Kakeya.lineOccupancyConstant_pos n)).ne'
        (ENNReal.ofReal_pos.mpr hell).ne').ne' hΩpos.ne'
  exact hpositive.not_ge hzero

theorem nikodym_hausdorffMeasure_ne_zero (hN : NikodymMaximalConjecture)
    {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hsn : s < n)
    {F Ω : Set (Space n)} (hΩ : MeasurableSet Ω) (hΩpos : 0 < volume Ω)
    {ell : ℝ} (hell : 0 < ell) (hF : HasNikodymSegments F Ω ell) :
    Measure.hausdorffMeasure s F ≠ 0 := by
  obtain ⟨Ω',hΩ',hsub,hpos,hfin⟩ := Measure.exists_subset_measure_lt_top hΩ hΩpos
  exact nikodym_hausdorffMeasure_ne_zero_finite hN hn hs hsn hΩ' hpos hfin hell
    (fun x hx => hF x (hsub hx))

/-- The full Hausdorff-dimension formulation of the geometric Nikodym
consequence. In fact no measurability assumption on the incidence set F
is needed; the set of passing points is measurable and has positive volume. -/
def NikodymDimensionConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ F Ω : Set (Space n), MeasurableSet Ω → 0 < volume Ω →
    ∀ ell : ℝ, 0 < ell → HasNikodymSegments F Ω ell → dimH F = n

theorem nikodymMaximal_implies_dimension (hN : NikodymMaximalConjecture) :
    NikodymDimensionConjecture := by
  intro n hn F Ω hΩ hΩpos ell hell hF
  apply le_antisymm
  · calc
      dimH F ≤ dimH (univ : Set (Space n)) := dimH_mono (subset_univ F)
      _ = n := by rw [Real.dimH_univ_eq_finrank]; simp only [Space,finrank_euclideanSpace_fin]
  · apply ENNReal.le_of_forall_nnreal_lt
    intro d hd
    by_cases hd0 : d = 0
    · simp [hd0]
    · have hdpos : 0 < (d:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd0)
      have hdn : (d:ℝ) < n := by exact_mod_cast hd
      exact le_dimH_of_hausdorffMeasure_ne_zero
        (nikodym_hausdorffMeasure_ne_zero hN hn hdpos hdn hΩ hΩpos hell hF)

end OAI.Geometry.Nikodym
