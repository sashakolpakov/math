import OAI.Analysis.PDE.Nonlinear.Segment
import OAI.Analysis.PDE.Nonlinear.AverageHolder
import OAI.Analysis.PDE.Nonlinear.AverageSmall

/-! The actual Moore linearization has uniform Hölder bounds on bounded Hessian fields. -/

noncomputable section
open Set _root_.MeasureTheory
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

local instance segmentHolderCoordinateComplete (n : ℕ) : CompleteSpace (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :=
  inferInstanceAs (CompleteSpace (EuclideanSpace ℝ (Fin n × Fin 4)))

local instance segmentHolderEndomorphismComplete (n : ℕ) :
    CompleteSpace (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :=
  ContinuousLinearMap.instCompleteSpace

theorem segmentOperator_eq_average {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    segmentOperator A B = segmentAverage OAI.Analysis.PDE.Dirichlet.detRealOperator A B := by
  unfold segmentOperator segmentAverage
  apply intervalIntegral.integral_congr
  intro t _
  apply congrArg (OAI.Analysis.PDE.Dirichlet.detRealOperator (n := n))
  simp only [segmentPoint, smul_sub, sub_smul, one_smul]
  abel

theorem segmentOperator_self {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    segmentOperator A A = OAI.Analysis.PDE.Dirichlet.detRealOperator A := by
  rw [segmentOperator_eq_average, segmentAverage_self]

theorem exists_segmentOperator_holder_bound {X : Type*} [MetricSpace X]
    (n : ℕ) {α R : ℝ} (hα : 0 < α) (hR : 0 ≤ R) :
    ∃ C ≥ 0, ∀ A B : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α,
      ‖A‖ ≤ R → ‖B‖ ≤ R →
      ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap X (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = segmentOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value B x)) ∧
        ‖H‖ ≤ C * (1 + ‖A‖ + ‖B‖) := by
  obtain ⟨C, hC, hc⟩ := exists_segmentAverage_holder_bound (X := X)
    (OAI.Analysis.PDE.Dirichlet.detRealOperator (n := n)) (OAI.Analysis.PDE.Dirichlet.contDiff_detRealOperator n 1) hα hR
  refine ⟨C, hC, ?_⟩
  intro A B hA hB
  obtain ⟨H, hH, hb⟩ := hc A B hA hB
  exact ⟨H, fun x => (hH x).trans (segmentOperator_eq_average _ _).symm, hb⟩

end OAI.Analysis.PDE.Nonlinear
