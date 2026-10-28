import OAI.Analysis.Fourier.SquareFunction.LocalSquare
import OAI.Analysis.Fourier.SquareFunction.EuclideanMaximal

open OAI.Analysis.Fourier.Wave

/-! Elementary, quantitative comparison between the actual coordinate cubes
used by the sharp-function proof and Euclidean balls. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory BoxIntegral Metric
open scoped ENNReal

noncomputable def cubeCorner {n : ℕ} (Q : Box (Fin n)) : Space n := WithLp.toLp 2 Q.upper

theorem dist_cubeCorner_le {n : ℕ} (Q : Box (Fin n)) {s : ℝ}
    (_ : 0 ≤ s) (hside : ∀ i, Q.upper i - Q.lower i = s)
    {x : Space n} (hx : x ∈ euclideanBox Q) :
    dist x (cubeCorner Q) ≤ (n : ℝ) * s := by
  have hd (i : Fin n) : ‖x i - Q.upper i‖ ≤ s := by
    have hi := hx i
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hi.2)]
    linarith [hi.1, hside i]
  calc
    _ = vectorNorm (fun i => x i - Q.upper i) := by rfl
    _ ≤ ∑ i, ‖x i - Q.upper i‖ := vectorNorm_le_sum_norm _
    _ ≤ ∑ _i : Fin n, s := Finset.sum_le_sum (fun i _ => hd i)
    _ = _ := by simp

theorem euclideanBox_subset_ball {n : ℕ} (Q : Box (Fin n)) {s : ℝ}
    (hs : 0 < s) (hside : ∀ i, Q.upper i - Q.lower i = s) :
    euclideanBox Q ⊆ ball (cubeCorner Q) (((n : ℝ) + 1) * s) := by
  intro x hx
  exact (dist_cubeCorner_le Q hs.le hside hx).trans_lt (by nlinarith)

theorem dist_le_cube_diameter {n : ℕ} (Q : Box (Fin n)) {s : ℝ}
    (hs : 0 ≤ s) (hside : ∀ i, Q.upper i - Q.lower i = s)
    {x z : Space n} (hx : x ∈ euclideanBox Q) (hz : z ∈ euclideanBox Q) :
    dist x z ≤ 2 * (n : ℝ) * s := by
  calc
    _ ≤ dist x (cubeCorner Q) + dist (cubeCorner Q) z := dist_triangle _ _ _
    _ = dist x (cubeCorner Q) + dist z (cubeCorner Q) := by rw [dist_comm (cubeCorner Q)]
    _ ≤ (n : ℝ) * s + (n : ℝ) * s :=
      add_le_add (dist_cubeCorner_le Q hs hside hx) (dist_cubeCorner_le Q hs hside hz)
    _ = _ := by ring

theorem volume_euclideanCube {n : ℕ} (Q : Box (Fin n)) {s : ℝ}
    (hside : ∀ i, Q.upper i - Q.lower i = s) :
    volume (euclideanBox Q) = ENNReal.ofReal s ^ n := by
  rw [volume_euclideanBox, Box.coe_eq_pi, Real.volume_pi_Ioc]
  simp only [hside, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem volume_enlarged_cube_ball {n : ℕ} (Q : Box (Fin n)) {s a : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hside : ∀ i, Q.upper i - Q.lower i = s) :
    volume (ball (cubeCorner Q) (a * s)) =
      (ENNReal.ofReal (a ^ n) * volume (ball (0 : Space n) 1)) * volume (euclideanBox Q) := by
  rw [show a * s = (a * s) * 1 by ring,
    Measure.addHaar_ball_mul_of_pos volume (cubeCorner Q) (mul_pos ha hs) 1,
    volume_euclideanCube Q hside]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin, mul_pow]
  rw [ENNReal.ofReal_mul (pow_nonneg ha.le _), ENNReal.ofReal_pow hs.le]
  ac_rfl

/-- Removing a sufficiently enlarged cube kills the input on a ball about
every point of the original cube, as required by the off-diagonal kernel bound. -/
theorem complement_enlarged_ball_vanishes {n : ℕ} (Q : Box (Fin n)) {s : ℝ}
    (hs : 0 < s) (hside : ∀ i, Q.upper i - Q.lower i = s)
    {z : Space n} (hz : z ∈ euclideanBox Q) (f : Space n → ℂ)
    {y : Space n} (hy : dist y z < 4 * (((n : ℝ) + 1) * s)) :
    (ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * s)))ᶜ.indicator f y = 0 := by
  have hzball := euclideanBox_subset_ball Q hs hside hz
  have hr : 0 < ((n : ℝ) + 1) * s := by positivity
  have hyball : y ∈ ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * s)) := by
    calc
      dist y (cubeCorner Q) ≤ dist y z + dist z (cubeCorner Q) := dist_triangle _ _ _
      _ < 4 * (((n : ℝ) + 1) * s) + (((n : ℝ) + 1) * s) := add_lt_add hy hzball
      _ < _ := by linarith
  exact Set.indicator_of_notMem (by simpa using hyball) f

end OAI.Analysis.Fourier.SquareFunction
