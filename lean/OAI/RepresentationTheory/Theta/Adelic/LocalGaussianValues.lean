import OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

/-! # Local Gaussian Values -/

namespace OAI.RepresentationTheory.Theta.Adelic.LocalGaussianValues

noncomputable section

/-! The constructed native Gaussian at a place is exactly the global
quadratic exponential restricted to that place's real position space. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.SiegelRestriction OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.DataTheta

theorem transpose_jacobi_pairing {I J : Type} [Fintype I] [Fintype J]
    (T : Matrix I J ℝ) (ξ : I → ℂ) (x : J → ℝ) :
    (∑ j, (x j : ℂ) * ((T.map Complex.ofRealHom).transpose.mulVec ξ j)) =
      ∑ i, (T.mulVec x i : ℂ) * ξ i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
    Complex.ofRealHom_eq_coe, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem localGaussian_real_value (v : Fin A.places) (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ)
    (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction (LocalPositionInclusion.localSiegelPeriod A P v z) (LocalPositionInclusion.localJacobiParameter A v ξ) x =
      DataTheta.gaussianValue (PeriodCoordinates.geometricPeriod A P z).matrix ξ (MinkowskiCoordinatesPosition.realPositionCoordinates A (Pi.single v x)) := by
  simp only [PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction, PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase, AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply,
    LocalPositionInclusion.localSiegelPeriod, SiegelRestriction.restrictedSiegel, LocalPositionInclusion.localJacobiParameter]
  rw [SiegelRestriction.realCongruence_form, transpose_jacobi_pairing, LocalPositionInclusion.realPositionColumn_apply]
  rfl

theorem nativeGaussian_real_value (v : Fin A.places) (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ)
    (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    (GeometricGaussians.nativeGaussian A P v z ξ).val (fun i => (A.real v).symm (x i)) =
      DataTheta.gaussianValue (PeriodCoordinates.geometricPeriod A P z).matrix ξ (MinkowskiCoordinatesPosition.realPositionCoordinates A (Pi.single v x)) := by
  rw [GeometricGaussians.nativeGaussian_apply]
  have hx : (fun i => A.real v ((A.real v).symm (x i))) = x := by
    funext i
    exact (A.real v).apply_symm_apply _
  rw [hx, localGaussian_real_value]

end

end OAI.RepresentationTheory.Theta.Adelic.LocalGaussianValues
