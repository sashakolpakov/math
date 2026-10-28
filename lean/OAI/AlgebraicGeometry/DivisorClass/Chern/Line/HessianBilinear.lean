import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorAlternationAction
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorHessian
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorConnectionOperator

/-! # Hessian Bilinear -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.HessianBilinear

noncomputable section

section

/-! The actual induced line connection on a covector-valued one-tensor, and its alternation and Hessian. -/

open _root_.ContinuousAlternatingMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance tensorConnection_formNormed (n : ℕ) : NormedAddCommGroup (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance
local instance tensorConnection_formSpace (n : ℕ) : NormedSpace ℝ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance
local instance tensorConnection_oneNormed (n : ℕ) : NormedAddCommGroup (E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance
local instance tensorConnection_oneSpace (n : ℕ) : NormedSpace ℝ (E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance

def lineCovectorTensorDerivative (n : ℕ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x v : E) : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  fderiv ℝ N x v - (N x).comp (G x v) - (Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (G x v)).comp (N x) + A x v • N x

theorem covectorTensor_column_derivative (n : ℕ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {x : E} (hN : DifferentiableAt ℝ N x) (v w : E) :
    fderiv ℝ (fun y => N y w) x v = fderiv ℝ N x v w := by
  have hd := ((ContinuousLinearMap.apply ℝ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) w).hasFDerivAt.comp x hN.hasFDerivAt).fderiv
  exact congrArg (fun T => T v) hd

theorem lineCovectorTensorDerivative_hessian (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {x : E} (ha : DifferentiableAt ℝ (ConnectionSymbols.lineCovectorConnectionDerivative n G A a) x) (v w : E) :
    lineCovectorTensorDerivative n G A (ConnectionSymbols.lineCovectorConnectionDerivative n G A a) x v w =
      CovectorHessian.lineCovectorHessian n G A a x v w := by
  unfold CovectorHessian.lineCovectorHessian
  rw [ConnectionSymbols.lineCovectorConnectionDerivative_apply, Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply,
    covectorTensor_column_derivative n _ ha v w]
  simp only [lineCovectorTensorDerivative, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply]
  abel

theorem covectorTensor_alternation_derivative (n : ℕ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {x : E} (hN : DifferentiableAt ℝ N x) (v : E) :
    fderiv ℝ (fun y => alternatizeUncurryFin (N y)) x v = alternatizeUncurryFin (fderiv ℝ N x v) := by
  have hd := ((alternatizeUncurryFinCLM ℝ E ℂ).hasFDerivAt.comp x hN.hasFDerivAt).fderiv
  exact congrArg (fun T => T v) hd

variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

theorem lineCovectorConnectionDerivative_alternation (b : Module.Basis ι ℝ E) (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {x : E} (hN : DifferentiableAt ℝ N x) (v : E) :
    ConnectionSymbols.lineCovectorConnectionDerivative (n + 1) G A (fun y => alternatizeUncurryFin (N y)) x v =
      alternatizeUncurryFin (lineCovectorTensorDerivative n G A N x v) := by
  rw [ConnectionSymbols.lineCovectorConnectionDerivative_apply, Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply,
    covectorTensor_alternation_derivative n N hN v, CovectorAlternationAction.covectorInfinitesimalAction_alternation b n]
  change alternatizeUncurryFinCLM ℝ E ℂ (fderiv ℝ N x v) -
      (alternatizeUncurryFinCLM ℝ E ℂ ((N x).comp (G x v)) +
        alternatizeUncurryFinCLM ℝ E ℂ ((Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (G x v)).comp (N x))) +
      A x v • alternatizeUncurryFinCLM ℝ E ℂ (N x) =
    alternatizeUncurryFinCLM ℝ E ℂ
      (fderiv ℝ N x v - (N x).comp (G x v) - (Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (G x v)).comp (N x) + A x v • N x)
  rw [map_add, map_sub, map_sub]
  have hs : alternatizeUncurryFinCLM ℝ E ℂ (A x v • N x) =
      A x v • alternatizeUncurryFinCLM ℝ E ℂ (N x) := alternatizeUncurryFin_smul _ _
  rw [hs]
  abel

end

/-! Bilinearity of the original covariant Hessian in its two tangent directions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] tensorConnection_formNormed tensorConnection_formSpace
  tensorConnection_oneNormed tensorConnection_oneSpace

def lineCovectorTensorScalarBilinear (n : ℕ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) (t : Fin n → E) : E →ₗ[ℝ] E →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (fun v w =>
    (fderiv ℝ N x v w - N x (G x v w) + CovectorConnectionOperator.lineCovectorConnectionOperator n (G x) (A x) v (N x w)) t)
    (fun v q w => by
      simp only [map_add, _root_.add_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
      abel)
    (fun r v w => by
      simp only [map_smul, _root_.smul_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply,
        ContinuousAlternatingMap.smul_apply]
      module)
    (fun v w q => by
      simp only [map_add, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply]
      abel)
    (fun r v w => by
      simp only [map_smul, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply,
        ContinuousAlternatingMap.smul_apply]
      module)

theorem lineCovectorTensorScalarBilinear_apply (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) (t : Fin n → E) (v w : E) :
    lineCovectorTensorScalarBilinear n G A N x t v w = lineCovectorTensorDerivative n G A N x v w t := by
  simp only [lineCovectorTensorScalarBilinear, LinearMap.mk₂_apply, lineCovectorTensorDerivative,
    CovectorConnectionOperator.lineCovectorConnectionOperator_apply, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply]
  abel

theorem lineCovectorHessian_scalar_bilinear (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {x : E} (ha : DifferentiableAt ℝ (ConnectionSymbols.lineCovectorConnectionDerivative n G A a) x)
    (t : Fin n → E) (v w : E) :
    CovectorHessian.lineCovectorHessian n G A a x v w t =
      lineCovectorTensorScalarBilinear n G A (ConnectionSymbols.lineCovectorConnectionDerivative n G A a) x t v w :=
  (congrArg (fun q : Analysis.DifferentialForms.Manifold.Basic.FormValue E n => q t) (lineCovectorTensorDerivative_hessian n G A a ha v w)).symm.trans
    (lineCovectorTensorScalarBilinear_apply n G A _ x t v w).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.HessianBilinear
