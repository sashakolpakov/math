import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldFinite
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCoordinates

/-! # Intrinsic Reference -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicReference.CM

noncomputable section

/-! Exact identification of native rational and completed theta sums
with the retained original finite Schwartz input in compatible coordinates. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)

def nativeOriginalFiniteInput (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m) :=
  FieldFinite.CM.sourceFieldFiniteInput A (Equiv.refl _) (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A) φ

theorem native_original_rational_theta (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (Z : Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℂ) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) (nativeOriginalFiniteInput A φ) Z ξ = RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta φ Z ξ := by
  have h := FieldFinite.CM.source_field_finite_theta_series A (Equiv.refl _) (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A) φ Z ξ
  refine Eq.trans ?_ h
  apply tsum_congr
  intro x
  change _ * RepresentationTheory.Theta.Adelic.DataTheta.gaussianValue Z ξ (fun i => (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ)) =
    _ * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel Z (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x) ξ
  congr 1
  simp only [RepresentationTheory.Theta.Adelic.DataTheta.gaussianValue, RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel, RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.realPosition, ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply]
  rfl

theorem native_completion_form_eq {I : Type*} [Fintype I] [DecidableEq I]
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    ((Real.pi : ℂ) / 2) • ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹) = Z.completionForm := by
  ext x y
  simp only [_root_.smul_apply, smul_eq_mul, ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear_apply,
    ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.completionForm_quadratic]

theorem native_original_completed_theta (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) (nativeOriginalFiniteInput A φ) Z.matrix ξ = RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  rw [RepresentationTheory.Theta.Adelic.DataTheta.completedTheta, native_completion_form_eq, native_original_rational_theta]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicReference.CM
