import OAI.RepresentationTheory.Theta.Adelic.GaussianProduct

/-! # Gaussian Evaluation -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.GaussianEvaluation

/-! Transfer a pointwise identity of actual archimedean Schwartz values
to the literal rational theta sum, retaining the actual finite weight. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition OAI.RepresentationTheory.Theta.Adelic.GaussianProduct.ThetaComparison

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem theta_of_arch_gaussian_value (φ : ThetaEvaluation.ArchimedeanTests F (3 * m))
    (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (Z : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ)
    (ξ : BallGeometryData.FrameIndex A → ℂ) (c : ℂ)
    (hv : ∀ x : BallGeometryData.RealPositions A, DataTheta.archTestValue (A := A) φ x =
      c * DataTheta.gaussianValue Z ξ (MinkowskiCoordinatesPosition.realPositionCoordinates A x)) :
    ThetaEvaluation.theta F (3 * m) φ f = c * DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) f Z ξ := by
  change (∑' q, ThetaEvaluation.summand F (3 * m) φ f q) =
    c * ∑' q, DataTheta.thetaSummand (GeometricGaussians.constructedComparison A P) f Z ξ q
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  change ThetaEvaluation.archimedeanValue F (3 * m) φ q * DataTheta.rationalWeight f q =
    c * (DataTheta.rationalWeight f q * DataTheta.gaussianValue Z ξ
      (fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A q i : ℝ)))
  rw [GaussianProduct.ThetaComparison.archimedeanValue_real_coordinates A, hv]
  have he := funext (MinkowskiCoordinatesPosition.realPositionCoordinates_rational A q)
  rw [he]
  ring

end RepresentationTheory.Theta.Adelic.GaussianEvaluation

namespace RepresentationTheory.Theta.Adelic.GaussianEvaluation.RationalThetaCovariance

/-! Rational SU covariance of the actual theta sum follows from its
adelic invariance and the pointwise archimedean Gaussian action. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction
open OAI.RepresentationTheory.Theta.Adelic.GaussianProduct.ThetaComparison OAI.RepresentationTheory.Theta.Adelic.GaussianEvaluation

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

theorem rationalTheta_covariance_of_gaussian_action
    (hds : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (g : SpecialUnitary.SU H.val) (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ)
    (J : ℂ) (hJ : J ≠ 0)
    (hv : ∀ x : BallGeometryData.RealPositions A,
      DataTheta.archTestValue (A := A)
        (SpecialUnitaryTheta.archimedeanAction F H K hd C P D (RationalSU.rationalArchimedeanSU F H g) (GeometricGaussians.gaussianFamily A P z ξ)) x =
      (J⁻¹ * Complex.exp (-(RealSymplecticAction.realSymplecticBlocks A P (RationalSU.rationalArchimedeanSU F H g)).thetaCorrectionForm
        (PeriodCoordinates.geometricPeriod A P z) ξ ξ)) *
      DataTheta.gaussianValue (PeriodCoordinates.geometricPeriod A P (GeometricGroup.geometricBallHom A (RationalSU.rationalArchimedeanSU F H g) • z)).matrix
        ((RealSymplecticAction.realSymplecticBlocks A P (RationalSU.rationalArchimedeanSU F H g)).jacobiChange (PeriodCoordinates.geometricPeriod A P z) ξ)
        (MinkowskiCoordinatesPosition.realPositionCoordinates A x)) :
    DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P)
      (FiniteSchwartz.finiteAction F H K hd C P D (RationalSU.rationalFiniteSU F H g) f)
      (PeriodCoordinates.geometricPeriod A P (GeometricGroup.geometricBallHom A (RationalSU.rationalArchimedeanSU F H g) • z)).matrix
      ((RealSymplecticAction.realSymplecticBlocks A P (RationalSU.rationalArchimedeanSU F H g)).jacobiChange (PeriodCoordinates.geometricPeriod A P z) ξ) =
      J * (Complex.exp ((RealSymplecticAction.realSymplecticBlocks A P (RationalSU.rationalArchimedeanSU F H g)).thetaCorrectionForm
        (PeriodCoordinates.geometricPeriod A P z) ξ ξ) *
        DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) f (PeriodCoordinates.geometricPeriod A P z).matrix ξ) := by
  have he := SpecialUnitaryTheta.rational_specialUnitary_theta F H K hd C P D hds hH hK g (GeometricGaussians.gaussianFamily A P z ξ) f
  rw [theta_of_arch_gaussian_value A P _ _ _ _ _ hv, ← GaussianProduct.ThetaComparison.rationalTheta_native A P] at he
  apply mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hJ) (Complex.exp_ne_zero _))
  calc
    _ = DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) f (PeriodCoordinates.geometricPeriod A P z).matrix ξ := he
    _ = _ := by
      rw [Complex.exp_neg]
      field_simp

end RepresentationTheory.Theta.Adelic.GaussianEvaluation.RationalThetaCovariance

end

end OAI
