import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicOscillatorIdentification
import OAI.RepresentationTheory.Theta.Adelic.GaussianEvaluation
import OAI.RepresentationTheory.Theta.Adelic.Covariance
import OAI.RepresentationTheory.Theta.Adelic.GeometricTensorCovariance

/-! # Intrinsic Fixed Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicFixedCovariance.CM

noncomputable section

section

/-! A fixed finite input gives the complete theta and tensor laws from
actual invariance of the adelic theta functional. The archimedean period
and Gaussian parameter remain arbitrary. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.GaussianProduct.ThetaComparison OAI.RepresentationTheory.Theta.Adelic.GaussianEvaluation
open OAI.RepresentationTheory.Theta.Adelic.Covariance OAI.RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)
  (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H W hd C P) (hC : C.ψ = FieldAdelicCharacter.CM.fieldAdelicCharacter F)
  (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
  (hfix : ∀ φ : RepresentationTheory.Theta.Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m),
    RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F (3 * m) (RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta.archimedeanAction F H W hd C P D g φ) f = RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F (3 * m) φ f)

include hC hfix in
theorem native_fixed_rational_theta_covariance (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) f
      (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)).matrix
      ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).jacobiChange (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z) ξ) =
    RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g z *
      (Complex.exp ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).thetaCorrectionForm (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z) ξ ξ) *
        RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) f (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix ξ) := by
  have he := hfix (RepresentationTheory.Theta.Adelic.GeometricGaussians.gaussianFamily A P z ξ)
  rw [RepresentationTheory.Theta.Adelic.GaussianEvaluation.theta_of_arch_gaussian_value A P _ _ _ _ _
    (IntrinsicGaussianCovariance.CM.native_full_gaussian_covariance A P hd C D hC g z ξ), ← RepresentationTheory.Theta.Adelic.GaussianProduct.ThetaComparison.rationalTheta_native A P] at he
  have hJ := (IntrinsicGaussianCocycle.CM.native_oscillator_factor_square A P hd C D hC g z).1
  apply mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hJ) (Complex.exp_ne_zero
    (-(RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).thetaCorrectionForm (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z) ξ ξ)))
  calc
    _ = RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) f (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix ξ := he
    _ = _ := by rw [Complex.exp_neg]; field_simp

include hC hfix in
theorem native_fixed_completed_theta_covariance (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) f
      (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)).matrix
      ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).jacobiChange (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z) ξ) =
    RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g z *
      RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) f (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix ξ := by
  rw [RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance.geometric_period_covariance]
  apply RepresentationTheory.Theta.Adelic.Covariance.completedTheta_covariance_of_theta A P
  intro η
  rw [← RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance.geometric_period_covariance]
  exact native_fixed_rational_theta_covariance A P hd C D hC g f hfix z η

include hC hfix in
theorem native_fixed_completed_tensor_covariance (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (a : ℕ)
    (v : Fin a → RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.completedTensor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) f a
      (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)).matrix
      (fun i => (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).jacobiChange (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z) (v i)) =
    RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D g z *
      RepresentationTheory.Theta.Adelic.DataTheta.completedTensor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) f a (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix v := by
  rw [RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance.geometric_period_covariance]
  apply RepresentationTheory.Theta.Adelic.Covariance.completedTensor_covariance_of_theta A P
  intro η
  rw [← RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance.geometric_period_covariance]
  exact native_fixed_rational_theta_covariance A P hd C D hC g f hfix z η

include hC hfix in
theorem native_fixed_geometric_tensor_covariance (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (a : ℕ)
    (v : Fin a → RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) f a (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)
      (fun i => RepresentationTheory.Theta.Adelic.BallGeometryData.dualFrameChange A g z (v i)) =
    RepresentationTheory.Theta.Adelic.BallNatural.Factors.naturalHalfFactor m (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g) z *
      RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) f a z v := by
  apply RepresentationTheory.Theta.Adelic.GeometricTensorCovariance.geometricTensor_covariance_of_completed A P
  intro w
  have h := native_fixed_completed_tensor_covariance A P hd C D hC g f hfix z a w
  rwa [IntrinsicOscillatorBranch.CM.native_oscillator_factor_eq_geometric A P hd C D hC] at h

end

/-! The complete geometric tensor law for every arithmetic datum on a
fixed rational tensor space, derived from invariance for all archimedean
tests of one fixed finite input. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Adelic.GeometricGroup OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)

def NativeGeometricThetaCovariant (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) : Prop :=
  ∀ (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (a : ℕ) (v : Fin a → RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ),
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) f a (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)
      (fun i => RepresentationTheory.Theta.Adelic.BallGeometryData.dualFrameChange A g z (v i)) =
    RepresentationTheory.Theta.Adelic.BallNatural.Factors.naturalHalfFactor m (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g) z * RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) f a z v

theorem native_geometric_theta_covariant_of_invariant
    (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
    (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H W hd C P) (hC : C.ψ = FieldAdelicCharacter.CM.fieldAdelicCharacter F)
    (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (hfix : ∀ φ : RepresentationTheory.Theta.Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m),
      RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F (3 * m) (RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta.archimedeanAction F H W hd C P D g φ) f = RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F (3 * m) φ f) :
    NativeGeometricThetaCovariant P g f := by
  intro A z a v
  exact native_fixed_geometric_tensor_covariance A P hd C D hC g f hfix z a v

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicFixedCovariance.CM
