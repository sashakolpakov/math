import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameAnalytic
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicAmbientRegularity
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorAnalytic

/-! # Intrinsic Parameter Tensor -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterTensor.Intrinsic

noncomputable section

/-! Actual completed native tensors in the local compact-place period
and half-determinant charts. These formulas recover the native tensor at
the reference choice and are jointly real analytic at positive periods. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise ContDiff

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameAnalytic.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicAmbientRegularity.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorAnalytic.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

def parameterTensor (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (a : ℕ)
    (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A)) : Adelic.DataTheta.TaylorTensor (A := A) a :=
  (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterHalfFrame B q)⁻¹ •
    (Adelic.DataTheta.completedTensor B f a (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B q)).compContinuousLinearMap
      (fun _ => IntrinsicTensorAnalytic.Intrinsic.matrixLinear (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B q)⁻¹ᵀ)

def parameterTopForm (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2))
    (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A)) : IntrinsicExterior.Intrinsic.TopCovector :=
  IntrinsicSecondProjection.Intrinsic.secondProjection (parameterTensor B f 2 q)

theorem parameter_tensor_base (hG : Adelic.DataTheta.GeometryIdentification B)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (a : ℕ) (z : Adelic.BallNatural.Ball) :
    parameterTensor B f a (IntrinsicCompactProjector.IntrinsicParameter.baseParameter A,z.val) = Adelic.DataTheta.geometricTensor B f a z := by
  unfold parameterTensor Adelic.DataTheta.geometricTensor
  rw [IntrinsicParameterGraph.IntrinsicHalfFrame.parameter_half_base B hG z,IntrinsicParameterGraph.Intrinsic.parameter_period_base B hG z,IntrinsicParameterGraph.IntrinsicHalfFrame.parameter_frame_base B hG z,
    Matrix.inv_eq_left_inv (B.frame z).inv_val]
  rfl

theorem parameter_top_base (hG : Adelic.DataTheta.GeometryIdentification B)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (z : Adelic.BallNatural.Ball) :
    parameterTopForm B f (IntrinsicCompactProjector.IntrinsicParameter.baseParameter A,z.val) = IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z := by
  unfold parameterTopForm IntrinsicSecondProjection.Intrinsic.thetaTopForm
  rw [parameter_tensor_base B hG f 2 z]

theorem parameter_tensor_analytic (hG : Adelic.DataTheta.GeometryIdentification B)
    (hL : Adelic.DataTheta.Descent.LatticeIdentification B) (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (a : ℕ) (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A))
    (hq : q ∈ IntrinsicParameterGraph.IntrinsicHalfFrame.parameterHalfDomain B)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) (hZ : IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B q = Z.matrix) :
    ContDiffAt ℝ ⊤ (parameterTensor B f a) q := by
  have ht : ContDiffAt ℝ ⊤ (Adelic.DataTheta.completedTensor B f a) (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B q) := by
    rw [hZ]
    exact IntrinsicAmbientRegularity.Intrinsic.completedTensor_ambient_contDiffAt B hE hL f a Z
  have hp := (IntrinsicFrameAnalytic.IntrinsicParameter.parameter_period_analytic B hG q hq.1).restrict_scalars ℝ
  have hm := IntrinsicFrameAnalytic.IntrinsicParameter.parameter_frame_analytic B hG q hq.1.1
  have hd : (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B q).det ≠ 0 := by
    rw [← IntrinsicParameterGraph.IntrinsicHalfFrame.parameter_half_square B hG q hq.1.1]
    exact pow_ne_zero _ (IntrinsicParameterGraph.IntrinsicHalfFrame.parameter_half_nonzero B hG q hq)
  have hl := (IntrinsicTensorAnalytic.Intrinsic.inverseTransposeLinear_analytic _ hm hd).restrict_scalars ℝ
  exact ((IntrinsicFrameAnalytic.IntrinsicParameter.parameter_half_analytic B hG q hq).restrict_scalars ℝ).inv
      (IntrinsicParameterGraph.IntrinsicHalfFrame.parameter_half_nonzero B hG q hq) |>.smul
    (IntrinsicTensorAnalytic.Intrinsic.tensor_precomposition_analytic a _ _ (ht.comp q hp) hl)

theorem parameter_top_analytic (hG : Adelic.DataTheta.GeometryIdentification B)
    (hL : Adelic.DataTheta.Descent.LatticeIdentification B) (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A))
    (hq : q ∈ IntrinsicParameterGraph.IntrinsicHalfFrame.parameterHalfDomain B)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) (hZ : IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B q = Z.matrix) :
    ContDiffAt ℝ ⊤ (parameterTopForm B f) q :=
  ((IntrinsicSecondProjection.Intrinsic.secondProjection (A := A)).restrictScalars ℝ).contDiff.contDiffAt.comp q
    (parameter_tensor_analytic B hG hL hE f 2 q hq Z hZ)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterTensor.Intrinsic
