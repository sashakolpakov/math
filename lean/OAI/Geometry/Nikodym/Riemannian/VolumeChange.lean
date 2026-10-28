import OAI.Geometry.Nikodym.Riemannian.Volume
import Mathlib.MeasureTheory.Function.Jacobian

open Set _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal Topology Matrix.Norms.Elementwise ContDiff
noncomputable section
namespace OAI.Geometry.Nikodym

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

def volumeOperatorMatrix (A : E →L[ℝ] E) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm A

theorem det_volumeOperatorMatrix (A : E →L[ℝ] E) :
    (volumeOperatorMatrix A).det = A.toLinearMap.det := by
  exact LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis A.toLinearMap

/-- The matrix determinant under a metric pullback is multiplied by the
square of the actual coordinate Jacobian. -/
theorem det_metric_pullback (A B J : E →L[ℝ] E)
    (h : ∀ u v,⟪A u,v⟫ = ⟪B (J u),J v⟫) :
    (volumeOperatorMatrix A).det = J.toLinearMap.det^2*(volumeOperatorMatrix B).det := by
  have hA : A = J.adjoint * B * J := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℝ
    intro v
    rw [h]
    exact (J.adjoint_inner_left v (B (J u))).symm
  have hm : volumeOperatorMatrix A =
      (volumeOperatorMatrix J).conjTranspose * volumeOperatorMatrix B * volumeOperatorMatrix J := by
    rw [hA]
    simp only [volumeOperatorMatrix,map_mul]
    congr 2
    exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm.map_star' J
  rw [hm,Matrix.det_mul,Matrix.det_mul,Matrix.det_conjTranspose,star_trivial,
    det_volumeOperatorMatrix J]
  ring

theorem sqrt_det_metric_pullback (A B J : E →L[ℝ] E)
    (h : ∀ u v,⟪A u,v⟫ = ⟪B (J u),J v⟫) :
    Real.sqrt (volumeOperatorMatrix A).det =
      |J.toLinearMap.det| * Real.sqrt (volumeOperatorMatrix B).det := by
  rw [det_metric_pullback A B J h,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]

namespace SmoothCoordinateMetric

theorem volumeDensity_pullback
    (g h : SmoothCoordinateMetric E) {F : E → E} {J : E → E →L[ℝ] E} {x : E}
    (hpull : ∀ u v,g.inner x u v = h.inner (F x) (J x u) (J x v)) :
    g.volumeDensity x = |(J x).toLinearMap.det| * h.volumeDensity (F x) :=
  sqrt_det_metric_pullback (g.coefficient x) (h.coefficient (F x)) (J x) hpull

end SmoothCoordinateMetric
end OAI.Geometry.Nikodym
