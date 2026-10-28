import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealFieldGaussian
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCharacterNormalization
import OAI.RepresentationTheory.Theta.Adelic.GaussianProduct

/-! # Intrinsic Gaussian Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCoordinates.CM

noncomputable section

/-! The constructed native Gaussian tests are exactly the transported
real Gaussians, and their product is the literal global Gaussian. -/

open scoped _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)

theorem native_gaussian_real_field (v : Fin A.places) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.GeometricGaussians.nativeGaussian A P v z ξ = RealFieldGaussian.CM.realFieldGaussian (A.real v) (A.real_continuous v)
      (A.real_inverse_continuous v) (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z) (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ξ) := by
  apply Subtype.ext
  funext x
  rfl

theorem native_gaussian_product_coordinates (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) (x : RepresentationTheory.Theta.Adelic.BallGeometryData.RealPositions A) :
    RepresentationTheory.Theta.Adelic.DataTheta.archTestValue (A := A) (RepresentationTheory.Theta.Adelic.GeometricGaussians.gaussianFamily A P z ξ) x =
      RepresentationTheory.Theta.Adelic.DataTheta.gaussianValue (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix ξ (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.realPositionCoordinates A x) :=
  RepresentationTheory.Theta.Adelic.GaussianProduct.archGaussian_product A P z ξ x

theorem native_real_trace_character (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
    (hC : C.ψ = FieldAdelicCharacter.CM.fieldAdelicCharacter F) (v : Fin A.places) :
    RepresentationTheory.Weil.Local.FieldFourier.Construction.fieldCharacter (A.real v) (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v))) = RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1 := by
  have : IsTotallyReal F := RepresentationTheory.Theta.Adelic.TotallyRealData.arithmetic_totally_real A
  apply AddChar.ext
  intro t
  change RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v)) ((A.real v).symm t) = RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1 t
  rw [hC, RealCharacterNormalization.CM.field_adelic_character_standard_real_coordinate, RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter_apply]
  congr 1
  push_cast
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCoordinates.CM
