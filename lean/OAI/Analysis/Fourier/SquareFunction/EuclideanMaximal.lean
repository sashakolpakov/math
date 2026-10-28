import OAI.Analysis.Fourier.SquareFunction.HardyLittlewood
import OAI.Analysis.Fourier.Wave.Basic

open OAI.Analysis.Fourier.Wave

/-! Euclidean specialization of the strong Hardy--Littlewood maximal theorem,
with the geometric constant supplied by Haar scaling, not an extra assumption. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Metric
open scoped ENNReal

theorem euclidean_ball_finite_pos {n : ℕ} (x : Space n) {r : ℝ} (hr : 0 < r) :
    volume (ball x r) ≠ 0 ∧ volume (ball x r) ≠ ∞ :=
  ⟨(measure_ball_pos volume x hr).ne', measure_ball_lt_top.ne⟩

theorem euclidean_ball_five {n : ℕ} (x : Space n) (r : ℝ) :
    volume (ball x (5 * r)) = ENNReal.ofReal ((5 : ℝ) ^ n) * volume (ball x r) := by
  rw [Measure.addHaar_ball_mul_of_pos volume x (by norm_num : (0 : ℝ) < 5) r,
    Measure.addHaar_ball_center volume x r]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin]

/-- The all-balls maximal estimate used twice in the combining-dilates proof,
at exponents `p` and `p/2`. -/
theorem eLpNorm_euclidean_ballMaximal_le {n : ℕ} {f : Space n → ℝ}
    (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p) :
    eLpNorm (ballMaximal volume (fun y => ENNReal.ofReal (f y))) (ENNReal.ofReal p) volume ≤
      (2 * ENNReal.ofReal ((5 : ℝ) ^ n * p / (p - 1)) ^ (1 / p)) *
        eLpNorm f (ENNReal.ofReal p) volume := by
  exact eLpNorm_ballMaximal_le volume hf hfn hp (by positivity)
    (fun x r hr => euclidean_ball_finite_pos x hr)
    (fun x r hr => (euclidean_ball_five x r).le)

theorem memLp_euclidean_ballMaximal {n : ℕ} {f : Space n → ℝ}
    (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p)
    (hfp : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (ballMaximal volume (fun y => ENNReal.ofReal (f y))) (ENNReal.ofReal p) volume := by
  exact memLp_ballMaximal volume hf hfn hp (D := (5 : ℝ) ^ n) (by positivity)
    (fun x r hr => euclidean_ball_finite_pos x hr)
    (fun x r hr => (euclidean_ball_five x r).le) hfp

end OAI.Analysis.Fourier.SquareFunction
