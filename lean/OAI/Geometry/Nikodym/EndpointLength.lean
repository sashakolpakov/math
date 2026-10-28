import OAI.Geometry.Nikodym.Beltrami.Length
import OAI.Geometry.Nikodym.EndpointFamily

noncomputable section
open Set Metric _root_.MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual length of the straight segment in the Beltrami metric. -/
def beltramiSegmentLength (κ : ℝ) (a b : E) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1,
    beltramiSpeed κ (AffineMap.lineMap a b t) (b-a)

theorem continuousAt_beltramiSpeed (κ : ℝ) {q : E × E}
    (hq : beltramiDenominator κ q.1 ≠ 0) :
    ContinuousAt (fun p : E × E => beltramiSpeed κ p.1 p.2) q := by
  unfold beltramiSpeed beltramiMetric
  apply ContinuousAt.sqrt
  apply ContinuousAt.div
  · unfold beltramiDenominator
    fun_prop
  · unfold beltramiDenominator
    fun_prop
  · exact pow_ne_zero 2 hq

theorem continuousOn_beltramiSegmentSpeed {κ : ℝ} {a b : E}
    (hq : ∀ t ∈ Icc (0 : ℝ) 1, beltramiDenominator κ (AffineMap.lineMap a b t) ≠ 0) :
    ContinuousOn (fun t : ℝ => beltramiSpeed κ (AffineMap.lineMap a b t) (b-a))
      (Icc (0 : ℝ) 1) := by
  intro t ht
  have hc : Continuous (fun t : ℝ => (AffineMap.lineMap a b t, b-a)) := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  exact ((continuousAt_beltramiSpeed κ (hq t ht)).comp hc.continuousAt).continuousWithinAt

theorem integrableOn_beltramiSegmentSpeed {κ : ℝ} {a b : E}
    (hq : ∀ t ∈ Icc (0 : ℝ) 1, beltramiDenominator κ (AffineMap.lineMap a b t) ≠ 0) :
    IntegrableOn (fun t : ℝ => beltramiSpeed κ (AffineMap.lineMap a b t) (b-a))
      (Icc (0 : ℝ) 1) :=
  (continuousOn_beltramiSegmentSpeed hq).integrableOn_compact isCompact_Icc

theorem beltramiSegmentLength_nonneg (κ : ℝ) (a b : E) :
    0 ≤ beltramiSegmentLength κ a b := by
  apply integral_nonneg
  intro t
  exact Real.sqrt_nonneg _

/-- The comparison uses the actual speed all along the segment. -/
theorem beltramiSegmentLength_bounds {κ : ℝ} {a b : E}
    (hsmall : ∀ t ∈ Icc (0 : ℝ) 1,
      |κ| * ‖AffineMap.lineMap a b t‖^2 ≤ 1/2) :
    dist a b / 4 ≤ beltramiSegmentLength κ a b ∧
      beltramiSegmentLength κ a b ≤ 3 * dist a b := by
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      beltramiDenominator κ (AffineMap.lineMap a b t) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (beltramiDenominator_small (hsmall t ht)).1)
  have hint := integrableOn_beltramiSegmentSpeed hq
  have hl := setIntegral_mono_on (integrableOn_const (C := (1/4)*‖b-a‖)
    (show volume (Icc (0 : ℝ) 1) ≠ ⊤ by simp)) hint measurableSet_Icc
    (fun t ht => (beltramiSpeed_small_bounds (hsmall t ht) (b-a)).1)
  have hu := setIntegral_mono_on hint (integrableOn_const (C := 3*‖b-a‖)
    (show volume (Icc (0 : ℝ) 1) ≠ ⊤ by simp)) measurableSet_Icc
    (fun t ht => (beltramiSpeed_small_bounds (hsmall t ht) (b-a)).2)
  have hn : ‖b-a‖ = dist a b := by rw [dist_eq_norm, norm_sub_rev]
  constructor
  · simpa [beltramiSegmentLength, hn, div_eq_mul_inv, mul_comm] using hl
  · simpa [beltramiSegmentLength, hn] using hu

theorem beltramiSegmentLength_bounds_of_closedBall {κ r : ℝ} {a b : E}
    (ha : a ∈ closedBall (0 : E) r) (hb : b ∈ closedBall (0 : E) r)
    (hsmall : ∀ x ∈ closedBall (0 : E) r, |κ| * ‖x‖^2 ≤ 1/2) :
    dist a b / 4 ≤ beltramiSegmentLength κ a b ∧
      beltramiSegmentLength κ a b ≤ 3 * dist a b :=
  beltramiSegmentLength_bounds (fun _ ht =>
    hsmall _ ((convex_closedBall (0 : E) r).lineMap_mem ha hb ht))

theorem dist_bounds_of_beltramiSegmentLength {κ r ell : ℝ} {a b : E}
    (ha : a ∈ closedBall (0 : E) r) (hb : b ∈ closedBall (0 : E) r)
    (hsmall : ∀ x ∈ closedBall (0 : E) r, |κ| * ‖x‖^2 ≤ 1/2)
    (hell : beltramiSegmentLength κ a b = ell) :
    ell/3 ≤ dist a b ∧ dist a b ≤ 4*ell := by
  obtain ⟨hlo,hup⟩ := beltramiSegmentLength_bounds_of_closedBall ha hb hsmall
  rw [hell] at hlo hup
  constructor <;> linarith

theorem beltramiSegmentLength_eq_intervalIntegral (κ : ℝ) (a b : E) :
    beltramiSegmentLength κ a b =
      ∫ t in (0 : ℝ)..1, beltramiSpeed κ (AffineMap.lineMap a b t) (b-a) := by
  rw [beltramiSegmentLength, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one]

theorem beltramiPathLength_segment_eq {κ : ℝ} {a b : E}
    (hq : ∀ t ∈ Icc (0 : ℝ) 1,
      beltramiDenominator κ (AffineMap.lineMap a b t) ≠ 0) :
    beltramiPathLength κ (AffineMap.lineMap a b) (fun _ => b-a) 0 1 =
      ENNReal.ofReal (beltramiSegmentLength κ a b) := by
  unfold beltramiPathLength beltramiSegmentLength
  symm
  apply ofReal_integral_eq_lintegral_ofReal (integrableOn_beltramiSegmentSpeed hq)
  exact Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _)

omit [InnerProductSpace ℝ E] in
theorem beltrami_small_on_closedBall {κ r : ℝ} (hr : 0 ≤ r)
    (hsmall : |κ| * r^2 ≤ 1/2) :
    ∀ x ∈ closedBall (0 : E) r, |κ| * ‖x‖^2 ≤ 1/2 := by
  intro x hx
  have hn : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
  exact (mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg x) hr |>.mpr hn)
    (abs_nonneg κ)).trans hsmall

end OAI.Geometry.Nikodym
