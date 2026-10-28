import OAI.Analysis.PDE.Nonlinear.Segment
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceCalculus

/-! Exact linear equation of the actual finite difference of a C² Moore solution. -/

noncomputable section
open Set InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Weak

theorem realHessian_differenceQuotient {n s : ℕ}
    (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hu : ContDiff ℝ 2 u)
    (v x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (h : ℝ) :
    OAI.Analysis.PDE.Dirichlet.realHessian (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x =
      h⁻¹ • (OAI.Analysis.PDE.Dirichlet.realHessian u (x + h • v) - OAI.Analysis.PDE.Dirichlet.realHessian u x) := by
  apply Matrix.ext
  intro i j
  simp only [OAI.Analysis.PDE.Dirichlet.realHessian, OAI.Analysis.PDE.Schauder.second_fderiv_differenceQuotient u hu,
    OAI.Analysis.PDE.Weak.differenceQuotient, smul_apply, sub_apply,
    Matrix.smul_apply, Matrix.sub_apply]

theorem quaternionHessian_differenceQuotient {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hu : ContDiff ℝ 2 u)
    (v x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (h : ℝ) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x =
      h⁻¹ • (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u (x + h • v) - OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  simp only [OAI.Analysis.PDE.Dirichlet.quaternionHessian, realHessian_differenceQuotient u hu,
    OAI.Analysis.Calculus.Quaternion.hessianMap_smul]
  congr 1
  exact (OAI.Analysis.PDE.Dirichlet.hessianMatrixLinear e).map_sub _ _

theorem moore_difference_equation {n : ℕ}
    (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hu : ContDiff ℝ 2 u)
    (v x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (h : ℝ)
    (hx : OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hx' : OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (x + h • v)) = f (x + h • v)) :
    OAI.Analysis.PDE.Elliptic.ellipticTrace (fun y => segmentOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (y + h • v))) (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x =
        OAI.Analysis.PDE.Weak.differenceQuotient v h f x := by
  have hd : ContDiff ℝ 2 (OAI.Analysis.PDE.Weak.differenceQuotient v h u) := OAI.Analysis.PDE.Schauder.contDiff_differenceQuotient u hu v h
  change OAI.Analysis.PDE.Elliptic.traceRight (fderiv ℝ (gradient (OAI.Analysis.PDE.Weak.differenceQuotient v h u)) x)
    (segmentOperator _ _) = _
  rw [segmentOperator_scaled_determinant_difference _ _ (h⁻¹) _
    (OAI.Analysis.PDE.Elliptic.fderiv_gradient_isSymmetric hd x)]
  · simp only [hx, hx', OAI.Analysis.PDE.Weak.differenceQuotient, smul_eq_mul]
  · rw [OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix_fderiv_gradient hd]
    exact quaternionHessian_differenceQuotient OAI.Analysis.Calculus.Quaternion.fourSlots u hu v x h

end OAI.Analysis.PDE.Nonlinear
