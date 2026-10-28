import OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarOperator
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! # Real Scalar Curvature Hessian -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarCurvatureHessian

noncomputable section

/-! The actual exterior derivative of the scalar Chern connection equals minus one half of the complex-line Hessian after multiplication by I. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem secondFDeriv_apply (f : E → ℝ) {x : E}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
  have hd := ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  exact congrArg (fun D : E →L[ℝ] ℝ => D w) hd

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem realScalarChern_curvature_hessian (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (x v : E) :
    (Complex.I * extDeriv (fun y => RealScalarOperator.realScalarChernOperator E (fderiv ℝ f y)) x ![v, Complex.I • v]).re =
      -(1 / 2 : ℝ) *
        (fderiv ℝ (fun y => fderiv ℝ f y v) x v +
          fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • v)) x (Complex.I • v)) := by
  have hds : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.contDiffAt.fderiv_right (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x := hds.differentiableAt (by simp)
  have hc := ((RealScalarOperator.realScalarChernOperator E).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => RealScalarOperator.realScalarChernOperator E (fderiv ℝ f y)) x =
    (RealScalarOperator.realScalarChernOperator E).comp (fderiv ℝ (fderiv ℝ f) x) at hc
  rw [ScalarOneFormDerivative.extDeriv_one_apply, hc]
  change (Complex.I *
    (RealScalarOperator.realScalarChernOperator E (fderiv ℝ (fderiv ℝ f) x v) (fun _ => Complex.I • v) -
      RealScalarOperator.realScalarChernOperator E (fderiv ℝ (fderiv ℝ f) x (Complex.I • v)) (fun _ => v))).re = _
  rw [RealScalarOperator.realScalarChernOperator_curvature_re, secondFDeriv_apply f hd, secondFDeriv_apply f hd]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarCurvatureHessian
