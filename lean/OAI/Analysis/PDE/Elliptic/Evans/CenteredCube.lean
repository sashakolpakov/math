import OAI.Analysis.PDE.Elliptic.Evans.BallExtrema

open Set Metric BoxIntegral
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def centeredCube (z : EuclideanSpace ℝ ι) (r : ℝ) (hr : 0 < r) : Box ι where
  lower i := z i - r
  upper i := z i + r
  lower_lt_upper i := by linarith

omit [Fintype ι] [Nonempty ι] in
theorem centeredCube_width (z : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r) (i : ι) :
    (centeredCube z r hr).upper i - (centeredCube z r hr).lower i = 2 * r := by
  dsimp [centeredCube]
  ring

omit [Fintype ι] [Nonempty ι] in
theorem centeredCube_center (z : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r) :
    cubeCenter (centeredCube z r hr) = z := by
  ext i
  change (z i - r + (z i + r)) / 2 = z i
  ring

omit [Nonempty ι] in
theorem closedBall_subset_centeredCube (z : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r) :
    closedBall z r ⊆ euclideanBox (centeredCube z (2 * r) (by positivity)) := by
  have h := ball_subset_euclideanBox (centeredCube z (2 * r) (by positivity))
    (centeredCube_width z (by positivity))
  rw [centeredCube_center] at h
  exact (closedBall_subset_ball (by linarith : r < 2 * r)).trans h

end OAI.Analysis.PDE.Elliptic
