import OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelGaussian
import OAI.RepresentationTheory.Weil.Local.FieldCoordinates
import OAI.RepresentationTheory.Weil.Local.RealTestSpace
import OAI.RepresentationTheory.Theta.Adelic.GeometricComparison

/-! # Geometric Gaussians -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

noncomputable section

/-! The native archimedean Gaussian tests are constructed from the
restriction of the actual period quadratic form to each real position
space, and transported through the specified completion isomorphisms. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.GeometricComparison

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def nativeGaussian (v : Fin A.places) (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ) :
    Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) (3 * m) :=
  Weil.Local.FieldCoordinates.Construction.testSpaceTransport (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv (A.real v) (A.real_continuous v)
    (A.real_inverse_continuous v) (3 * m)).symm
    (Weil.Local.RealTestSpace.Construction.realSchwartzToBruhat
      (AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelGaussian.CM.siegelGaussianSchwartz (LocalPositionInclusion.localSiegelPeriod A P v z) (LocalPositionInclusion.localJacobiParameter A v ξ)))

theorem nativeGaussian_apply (v : Fin A.places) (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ)
    (x : Weil.Local.FunctionsMetaplectic.Construction.Position (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) (3 * m)) :
    (nativeGaussian A P v z ξ).val x = PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction (LocalPositionInclusion.localSiegelPeriod A P v z)
      (LocalPositionInclusion.localJacobiParameter A v ξ) (fun i => A.real v (x i)) :=
  AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelGaussian.CM.siegel_gaussian_schwartz_apply _ _ _

def gaussianFamily (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ) : ThetaEvaluation.ArchimedeanTests F (3 * m) :=
  Equiv.piCongrLeft (fun v : NumberField.InfinitePlace F => Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) (3 * m))
    A.enumerate (fun v => nativeGaussian A P v z ξ)

theorem gaussianFamily_enumerate (v : Fin A.places) (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ) :
    gaussianFamily A P z ξ (A.enumerate v) = nativeGaussian A P v z ξ :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem nativeGaussian_at_zero (v : Fin A.places) (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ) :
    (nativeGaussian A P v z ξ).val 0 = 1 := by
  rw [nativeGaussian_apply]
  simp [PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction, PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase, AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply,
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply]

def constructedComparison : DataTheta.ComparisonData F H K A :=
  GeometricComparison.geometricComparison A P (gaussianFamily A P)

theorem constructedComparison_coordinates : DataTheta.CoordinateIdentification (constructedComparison A P) P :=
  GeometricComparison.geometricComparison_coordinates A P (gaussianFamily A P)

theorem constructedComparison_geometry : DataTheta.GeometryIdentification (constructedComparison A P) :=
  GeometricComparison.geometricComparison_geometry A P (gaussianFamily A P)

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
