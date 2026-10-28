import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Elliptic Extension -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticExtension.CM.Construction

noncomputable section

/-! Extending local elliptic coefficients by the identity for a supported
Dirichlet problem preserves boundedness and uniform positivity. -/

open _root_.MeasureTheory Set

variable {α G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

def ellipticFieldExtension (K : Set α) (A : α → G →L[ℝ] G) : α → G →L[ℝ] G := by
  classical
  exact K.piecewise A (fun _ => ContinuousLinearMap.id ℝ G)

theorem ellipticFieldExtension_of_mem (K : Set α) (A : α → G →L[ℝ] G) {x : α} (hx : x ∈ K) :
    ellipticFieldExtension K A x = A x := by
  classical
  exact Set.piecewise_eq_of_mem K A _ hx

theorem ellipticFieldExtension_of_notMem (K : Set α) (A : α → G →L[ℝ] G) {x : α} (hx : x ∉ K) :
    ellipticFieldExtension K A x = ContinuousLinearMap.id ℝ G := by
  classical
  exact Set.piecewise_eq_of_notMem K A _ hx

theorem ellipticFieldExtension_bound (K : Set α) (A : α → G →L[ℝ] G)
    {C : ℝ} (hC : ∀ x ∈ K, ‖A x‖ ≤ C) (x : α) :
    ‖ellipticFieldExtension K A x‖ ≤ max C 1 := by
  by_cases hx : x ∈ K
  · rw [ellipticFieldExtension_of_mem K A hx]
    exact (hC x hx).trans (le_max_left _ _)
  · rw [ellipticFieldExtension_of_notMem K A hx]
    exact ContinuousLinearMap.norm_id_le.trans (le_max_right _ _)

theorem ellipticFieldExtension_lower_bound (K : Set α) (A : α → G →L[ℝ] G)
    {c : ℝ} (hc : ∀ x ∈ K, ∀ w : G, c * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w) (x : α) (w : G) :
    min c 1 * ‖w‖ * ‖w‖ ≤ inner ℝ (ellipticFieldExtension K A x w) w := by
  by_cases hx : x ∈ K
  · rw [ellipticFieldExtension_of_mem K A hx]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left c 1) (norm_nonneg w)) (norm_nonneg w)).trans (hc x hx w)
  · rw [ellipticFieldExtension_of_notMem K A hx, ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
    calc
      min c 1 * ‖w‖ * ‖w‖ ≤ 1 * ‖w‖ * ‖w‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_right c 1) (norm_nonneg w)) (norm_nonneg w)
      _ = ‖w‖ ^ 2 := by ring

variable [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [FiniteDimensional ℝ G]

theorem ellipticFieldExtension_aestronglyMeasurable (K : Set α) (A : α → G →L[ℝ] G)
    (hK : MeasurableSet K) (hA : ContinuousOn A K) (μ : Measure α) :
    AEStronglyMeasurable (ellipticFieldExtension K A) μ := by
  classical
  borelize (G →L[ℝ] G)
  exact (hA.measurable_piecewise continuousOn_const hK).aestronglyMeasurable

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticExtension.CM.Construction
