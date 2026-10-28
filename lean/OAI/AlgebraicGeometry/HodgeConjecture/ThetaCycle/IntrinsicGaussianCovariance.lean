import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCocycle
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicJacobi

/-! # Intrinsic Gaussian Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCovariance.CM

noncomputable section

/-! Full Jacobi covariance of the actual native Gaussian family,
including its exact global quadratic exponential and coefficient. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition

local instance nativeFullGaussianMeasurable (F : Type) [Field F] [NumberField F]
    (v : NumberField.InfinitePlace F) : MeasurableSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance nativeFullGaussianBorel (F : Type) [Field F] [NumberField F]
    (v : NumberField.InfinitePlace F) : BorelSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩
local instance nativeFullGaussianSecondCountable (F : Type) [Field F] [NumberField F]
    (v : NumberField.InfinitePlace F) : SecondCountableTopology (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := by
  have : CharZero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inl v)
  exact RepresentationTheory.Weil.UnitarySplitting.TestSpaceAnalysis.Construction.localField_secondCountable _ (RepresentationTheory.Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F (.inl v))

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)
  (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H W hd C P) (hC : C.ψ = FieldAdelicCharacter.CM.fieldAdelicCharacter F)

include hC in
theorem native_local_full_gaussian_covariance (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places)
    (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) (3 * m)
      (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v)))
      (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl (A.enumerate v)) (g (A.enumerate v))) (RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v z ξ) =
    (IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v z *
      Complex.exp (-(IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).thetaCorrectionForm (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)
        (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ξ) (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ξ))) •
      RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)
        ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).jacobiChange (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z) ξ) := by
  let a := RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl (A.enumerate v)) (g (A.enumerate v))
  have hz : RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v z 0 = RealFieldGaussian.CM.realFieldGaussian (A.real v) (A.real_continuous v)
      (A.real_inverse_continuous v) (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z) 0 := by
    simpa only [RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter, Matrix.mulVec_zero] using IntrinsicGaussianCoordinates.CM.native_gaussian_real_field A P v z 0
  have hc : RealFieldGaussian.CM.realFieldGaussianCoefficient (A.real v) (A.real_continuous v) (A.real_inverse_continuous v)
      (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v))) a (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z) =
      IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v z := by
    unfold IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient
    rw [hz]
    rfl
  have h := RealFieldGaussian.CM.real_field_gaussian_covariance (A.real v) (A.real_continuous v) (A.real_inverse_continuous v)
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v))) (IntrinsicGaussianCoordinates.CM.native_real_trace_character A C hC v)
    a (OscillatorPhaseOrder.CM.swapSymplecticPhase (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v))
    ((IntrinsicRealGaussianAction.CM.native_local_projection_real A P hd C D g v).trans
      (OscillatorPhaseOrder.CM.swap_symplectic_phase_involutive (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v)).symm)
    (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z) (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ξ)
  rw [IntrinsicGaussianCoordinates.CM.native_gaussian_real_field, IntrinsicGaussianCoordinates.CM.native_gaussian_real_field,
    IntrinsicJacobi.CM.native_local_period_covariance, IntrinsicJacobi.CM.native_local_jacobi_covariance]
  simpa only [hc] using! h

include hC in
theorem native_full_gaussian_covariance (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H)
    (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) (x : RepresentationTheory.Theta.Adelic.BallGeometryData.RealPositions A) :
    RepresentationTheory.Theta.Adelic.DataTheta.archTestValue (A := A) (RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta.archimedeanAction F H W hd C P D g (RepresentationTheory.Theta.Adelic.GeometricGaussians.gaussianFamily A P z ξ)) x =
      (RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g z)⁻¹ *
        Complex.exp (-(RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).thetaCorrectionForm (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z) ξ ξ) *
        RepresentationTheory.Theta.Adelic.DataTheta.gaussianValue (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)).matrix
          ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).jacobiChange (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z) ξ) (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.realPositionCoordinates A x) := by
  rw [← IntrinsicGaussianCoordinates.CM.native_gaussian_product_coordinates A P, IntrinsicGaussianCocycle.CM.native_oscillator_factor_product, inv_inv]
  simp only [RepresentationTheory.Theta.Adelic.DataTheta.archTestValue, RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta.archimedeanAction, RepresentationTheory.Theta.Adelic.GeometricGaussians.gaussianFamily_enumerate,
    native_local_full_gaussian_covariance A P hd C D hC]
  change (∏ v, (IntrinsicRealGaussianAction.CM.nativeLocalGaussianCoefficient A P hd C D g v z *
    Complex.exp (-(IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).thetaCorrectionForm (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)
      (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ξ) (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ξ))) *
    (RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)
      ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).jacobiChange (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z) ξ)).val
      (fun i => (A.real v).symm (x v i))) = _
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum,
    Finset.sum_neg_distrib, ← IntrinsicJacobi.CM.native_theta_correction_sum]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCovariance.CM
