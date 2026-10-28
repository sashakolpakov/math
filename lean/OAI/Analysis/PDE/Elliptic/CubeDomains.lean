import OAI.Analysis.PDE.Elliptic.CubeParents

open Set BoxIntegral
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A single enlarged root ball contains all balls needed to apply
the growth lemma in dyadic subcubes. -/
theorem cube_growth_domain_subset {B C : Box ι} {r R : ℝ} (hCB : C ≤ B)
    (_ : 0 < r) (hR : 0 < R)
    (hC : ∀ i, C.upper i - C.lower i = 2 * r)
    (hB : ∀ i, B.upper i - B.lower i = 2 * R) :
    Metric.closedBall (cubeCenter C) (2 * (3 * (Fintype.card ι : ℝ)) * r) ⊆
      Metric.ball (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R) := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hcenter := euclideanBox_subset_closedBall B hR.le hB
    (euclideanBox_mono hCB (cubeCenter_mem_euclideanBox C))
  have hrr := cube_halfwidth_le_of_le hCB hC hB
  have hscale := mul_le_mul_of_nonneg_left hrr
    (show 0 ≤ 6 * (Fintype.card ι : ℝ) by positivity)
  intro x hx
  rw [Metric.mem_ball]
  rw [Metric.mem_closedBall] at hx hcenter
  have htri := dist_triangle x (cubeCenter C) (cubeCenter B)
  have hdR := mul_pos hd hR
  nlinarith

omit [Fintype ι] [Nonempty ι] in
theorem dyadicBox_halfwidth (B : Box ι) {r : ℝ}
    (hB : ∀ i, B.upper i - B.lower i = 2 * r) (w : List (Set ι)) (i : ι) :
    (dyadicBox B w).upper i - (dyadicBox B w).lower i =
      2 * (r / (2 : ℝ) ^ w.length) := by
  rw [dyadicBox_width, hB]
  ring

omit [Fintype ι] [Nonempty ι] in
theorem dyadicBox_parent_halfwidth (B : Box ι) {r : ℝ}
    (hB : ∀ i, B.upper i - B.lower i = 2 * r) (w : List (Set ι)) (i : ι) :
    (dyadicBox B w).upper i - (dyadicBox B w).lower i =
      4 * (r / (2 : ℝ) ^ (w.length + 1)) := by
  rw [dyadicBox_halfwidth B hB, pow_succ]
  ring

end OAI.Analysis.PDE.Elliptic
