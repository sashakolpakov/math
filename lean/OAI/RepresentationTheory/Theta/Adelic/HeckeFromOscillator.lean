import OAI.RepresentationTheory.Theta.Adelic.GaussianEvaluation
import OAI.RepresentationTheory.Theta.Adelic.Covariance
import OAI.RepresentationTheory.Theta.Adelic.GeometricTensorCovariance
import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Hecke From Oscillator -/

namespace OAI.RepresentationTheory.Theta.Adelic.HeckeFromOscillator

noncomputable section

/-! Assemble all rational Hecke laws from the actual oscillator
identification, adelic invariance, and the independently proved frame
and completed-theta comparisons. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame OAI.RepresentationTheory.Theta.Adelic.GeometricAutomorphy OAI.RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction
open OAI.RepresentationTheory.Theta.Adelic.GaussianEvaluation.RationalThetaCovariance OAI.RepresentationTheory.Theta.Adelic.Covariance OAI.RepresentationTheory.Theta.Adelic.GeometricTensorCovariance

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

theorem oscillatorFactor_eq_geometric_of_line
    (hO : DataTheta.OscillatorIdentification (GeometricGaussians.constructedComparison A P) P hd C D)
    (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    DataTheta.oscillatorFactor (GeometricGaussians.constructedComparison A P) P hd C D g z = GeometricAutomorphy.geometricFactor A P g z := by
  have hs := hO.2.2.2.2.2.2.2.2.1 g z 1
  change (DataTheta.oscillatorFactor (GeometricGaussians.constructedComparison A P) P hd C D g z * GeometricHalfFrame.geometricHalfFrame A P z /
    GeometricHalfFrame.geometricHalfFrame A P (GeometricGroup.geometricBallHom A g • z)) * 1 =
    BallNatural.Factors.naturalHalfFactor m (GeometricGroup.geometricBallHom A g) z * 1 at hs
  simp only [mul_one] at hs
  change DataTheta.oscillatorFactor (GeometricGaussians.constructedComparison A P) P hd C D g z =
    BallNatural.Factors.naturalHalfFactor m (GeometricGroup.geometricBallHom A g) z * GeometricHalfFrame.geometricHalfFrame A P (GeometricGroup.geometricBallHom A g • z) /
      GeometricHalfFrame.geometricHalfFrame A P z
  apply (eq_div_iff (GeometricHalfFrame.geometricHalfFrame_nonzero A P z)).mpr
  exact (div_eq_iff (GeometricHalfFrame.geometricHalfFrame_nonzero A P (GeometricGroup.geometricBallHom A g • z))).mp hs

theorem constructedComparison_hecke_of_oscillator
    (hds : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (hO : DataTheta.OscillatorIdentification (GeometricGaussians.constructedComparison A P) P hd C D) :
    DataTheta.Descent.RationalHeckeCovariance (GeometricGaussians.constructedComparison A P) P hd C D := by
  rcases hO with ⟨hprod, hmeta, hn, hholo, hc, hmul, hone, hval, hline, hchar⟩
  have hO : DataTheta.OscillatorIdentification (GeometricGaussians.constructedComparison A P) P hd C D :=
    ⟨hprod, hmeta, hn, hholo, hc, hmul, hone, hval, hline, hchar⟩
  intro g f
  let gA := RationalSU.rationalArchimedeanSU F H g
  let fnew := FiniteSchwartz.finiteAction F H K hd C P D (RationalSU.rationalFiniteSU F H g) f
  let J := fun z => DataTheta.oscillatorFactor (GeometricGaussians.constructedComparison A P) P hd C D gA z
  have hp (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ) :
      DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) fnew
        (PeriodCoordinates.geometricPeriod A P (GeometricGroup.geometricBallHom A gA • z)).matrix
        ((RealSymplecticAction.realSymplecticBlocks A P gA).jacobiChange (PeriodCoordinates.geometricPeriod A P z) ξ) =
      J z * (Complex.exp ((RealSymplecticAction.realSymplecticBlocks A P gA).thetaCorrectionForm (PeriodCoordinates.geometricPeriod A P z) ξ ξ) *
        DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) f (PeriodCoordinates.geometricPeriod A P z).matrix ξ) := by
    apply GaussianEvaluation.RationalThetaCovariance.rationalTheta_covariance_of_gaussian_action A P hd C D hds hH hK g f z ξ (J z) ((hn gA z).1)
    intro x
    exact hval gA z ξ x
  have hpc (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ) :
      DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) fnew
        ((RealSymplecticAction.realSymplecticBlocks A P gA).transformSiegel (PeriodCoordinates.geometricPeriod A P z)).matrix
        ((RealSymplecticAction.realSymplecticBlocks A P gA).jacobiChange (PeriodCoordinates.geometricPeriod A P z) ξ) =
      J z * (Complex.exp ((RealSymplecticAction.realSymplecticBlocks A P gA).thetaCorrectionForm (PeriodCoordinates.geometricPeriod A P z) ξ ξ) *
        DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) f (PeriodCoordinates.geometricPeriod A P z).matrix ξ) := by
    rw [← CoordinateFrameAction.PeriodCovariance.geometric_period_covariance A P gA z]
    exact hp z ξ
  have ht (a : ℕ) (z : BallNatural.Ball) (v : Fin a → BallGeometryData.FrameIndex A → ℂ) :
      DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) fnew a
        (PeriodCoordinates.geometricPeriod A P (GeometricGroup.geometricBallHom A gA • z)).matrix
        (fun i => (RealSymplecticAction.realSymplecticBlocks A P gA).jacobiChange (PeriodCoordinates.geometricPeriod A P z) (v i)) =
      J z * DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a (PeriodCoordinates.geometricPeriod A P z).matrix v := by
    rw [CoordinateFrameAction.PeriodCovariance.geometric_period_covariance A P gA z]
    exact Covariance.completedTensor_covariance_of_theta A P f fnew (RealSymplecticAction.realSymplecticBlocks A P gA)
      (PeriodCoordinates.geometricPeriod A P z) (J z) (hpc z) a v
  refine ⟨hp, ?_, ht, ?_⟩
  · intro z ξ
    change DataTheta.completedTheta (GeometricGaussians.constructedComparison A P) fnew
      (PeriodCoordinates.geometricPeriod A P (GeometricGroup.geometricBallHom A gA • z)).matrix
      ((RealSymplecticAction.realSymplecticBlocks A P gA).jacobiChange (PeriodCoordinates.geometricPeriod A P z) ξ) =
      J z * DataTheta.completedTheta (GeometricGaussians.constructedComparison A P) f (PeriodCoordinates.geometricPeriod A P z).matrix ξ
    rw [CoordinateFrameAction.PeriodCovariance.geometric_period_covariance A P gA z]
    exact Covariance.completedTheta_covariance_of_theta A P f fnew (RealSymplecticAction.realSymplecticBlocks A P gA)
      (PeriodCoordinates.geometricPeriod A P z) (J z) (hpc z) ξ
  · intro a z v
    apply GeometricTensorCovariance.geometricTensor_covariance_of_completed A P f fnew gA z a
    intro w
    have he := ht a z w
    rw [show J z = GeometricAutomorphy.geometricFactor A P gA z from oscillatorFactor_eq_geometric_of_line A P hd C D hO gA z] at he
    exact he

end

end OAI.RepresentationTheory.Theta.Adelic.HeckeFromOscillator
