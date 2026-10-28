import OAI.Analysis.PDE.Nonlinear.SegmentHolder
import OAI.Analysis.PDE.Nonlinear.ShiftedAverage
import OAI.Analysis.PDE.Nonlinear.Difference
import OAI.Analysis.PDE.Nonlinear.FamilyFreeze

/-! The actual uniformly Hölder family linearizing a C²,α Moore solution. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Weak

local instance mooreFamilyCoordinateComplete (n : ℕ) : CompleteSpace (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :=
  inferInstanceAs (CompleteSpace (EuclideanSpace ℝ (Fin n × Fin 4)))
local instance mooreFamilyEndomorphismComplete (n : ℕ) :
    CompleteSpace (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :=
  ContinuousLinearMap.instCompleteSpace

theorem exists_moore_difference_family {n : ℕ} {α : ℝ} (hα : 0 < α)
    (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hu : ContDiff ℝ 2 u)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α)
    (hH : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)
    (v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :
    ∃ A : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
        (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) α,
      (∀ h x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x = segmentOperator
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (x + h • v))) ∧
      (∃ M ≥ 0, ∀ h, ‖A h‖ ≤ M) ∧
      (∀ x, Tendsto (fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x) (𝓝 0)
        (𝓝 (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)))) ∧
      (∀ h x, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x →
        OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (x + h • v)) = f (x + h • v) →
        OAI.Analysis.PDE.Elliptic.ellipticTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h)) (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x =
          OAI.Analysis.PDE.Weak.differenceQuotient v h f x) := by
  obtain ⟨A, hA, hbound, hlim⟩ := exists_shifted_average_family
    (OAI.Analysis.PDE.Dirichlet.detRealOperator (n := n)) (OAI.Analysis.PDE.Dirichlet.contDiff_detRealOperator n 1) hα H v
  have hval (h : ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x = segmentOperator
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (x + h • v)) := by
    rw [hA h x, hH x, hH (x + h • v), ← segmentOperator_eq_average]
  refine ⟨A, hval, hbound, ?_, ?_⟩
  · intro x
    simpa only [hH x] using hlim x
  · intro h x hx hx'
    have he : OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) = fun y => segmentOperator
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (y + h • v)) :=
      funext (hval h)
    rw [he]
    exact moore_difference_equation u f hu v x h hx hx'

end OAI.Analysis.PDE.Nonlinear
