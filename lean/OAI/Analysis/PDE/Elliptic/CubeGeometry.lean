import OAI.Analysis.PDE.Elliptic.DyadicCover
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open Set BoxIntegral _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def euclideanBox (B : Box ι) : Set (EuclideanSpace ℝ ι) := WithLp.ofLp ⁻¹' (B : Set (ι → ℝ))

def cubeCenter (B : Box ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i ↦ (B.lower i + B.upper i) / 2)

theorem norm_euclidean_le_card_mul (x : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 ≤ r)
    (hx : ∀ i, ‖x i‖ ≤ r) : ‖x‖ ≤ (Fintype.card ι : ℝ) * r := by
  have hd : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := ι)))
  have hs : ‖x‖ ^ 2 ≤ (Fintype.card ι : ℝ) * r ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : ι, r ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (hx i) 2
      _ = _ := by simp
  have hdd : (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hdd (sq_nonneg r)
  have hp : 0 ≤ (Fintype.card ι : ℝ) * r := by positivity
  nlinarith [norm_nonneg x]

omit [Nonempty ι] in
theorem ball_subset_euclideanBox (B : Box ι) {r : ℝ}
    (hwidth : ∀ i, B.upper i - B.lower i = 2 * r) :
    Metric.ball (cubeCenter B) r ⊆ euclideanBox B := by
  intro x hx
  have hn : ‖x - cubeCenter B‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  change ∀ i, B.lower i < x i ∧ x i ≤ B.upper i
  intro i
  have ha := PiLp.norm_apply_le (x - cubeCenter B) i
  change |x i - (B.lower i + B.upper i) / 2| ≤ ‖x - cubeCenter B‖ at ha
  have hab := abs_lt.mp (ha.trans_lt hn)
  constructor <;> linarith [hwidth i, hab.1, hab.2]

theorem euclideanBox_subset_closedBall (B : Box ι) {r : ℝ} (hr : 0 ≤ r)
    (hwidth : ∀ i, B.upper i - B.lower i = 2 * r) :
    euclideanBox B ⊆ Metric.closedBall (cubeCenter B) ((Fintype.card ι : ℝ) * r) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  apply norm_euclidean_le_card_mul _ hr
  intro i
  change |x i - (B.lower i + B.upper i) / 2| ≤ r
  have hxi : B.lower i < x i ∧ x i ≤ B.upper i := hx i
  rw [abs_le]
  constructor <;> linarith [hwidth i, hxi.1, hxi.2]

omit [Nonempty ι] in
theorem volume_euclideanBox (B : Box ι) :
    volume (euclideanBox B) = volume (B : Set (ι → ℝ)) :=
  (PiLp.volume_preserving_ofLp ι).measure_preimage B.measurableSet_coe.nullMeasurableSet

end OAI.Analysis.PDE.Elliptic
