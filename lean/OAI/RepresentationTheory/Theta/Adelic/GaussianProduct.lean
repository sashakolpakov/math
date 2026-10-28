import OAI.RepresentationTheory.Theta.Adelic.PeriodCrossTerms
import OAI.RepresentationTheory.Theta.Adelic.LocalGaussianValues

/-! # Gaussian Product -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.GaussianProduct

/-! The product of the constructed native archimedean Gaussian tests
is the requested global Siegel Gaussian in the actual real coordinates. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion OAI.RepresentationTheory.Theta.Adelic.PeriodCrossTerms
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.LocalGaussianValues

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem realPosition_sum_columns (x : BallGeometryData.RealPositions A) :
    MinkowskiCoordinatesPosition.realPositionCoordinates A x = ∑ v, (LocalPositionInclusion.realPositionColumn A v).mulVec (x v) := by
  simp only [LocalPositionInclusion.realPositionColumn_apply, ← map_sum]
  congr 1
  ext v j
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single v]
  · rw [Pi.single_eq_same]
  · intro w _ hw
    simp [Ne.symm hw]
  · intro hv
    exact (hv (Finset.mem_univ v)).elim

theorem period_quadratic_sum (z : BallNatural.Ball) (x : BallGeometryData.RealPositions A) :
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (PeriodCoordinates.geometricPeriod A P z).matrix
      (MinkowskiCoordinatesPosition.realPositionCoordinates A x) (MinkowskiCoordinatesPosition.realPositionCoordinates A x) =
      ∑ v, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (PeriodCoordinates.geometricPeriod A P z).matrix
        ((LocalPositionInclusion.realPositionColumn A v).mulVec (x v)) ((LocalPositionInclusion.realPositionColumn A v).mulVec (x v)) := by
  rw [realPosition_sum_columns]
  simp only [map_sum, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_eq_single v
  · intro w _ hw
    exact PeriodCrossTerms.period_cross_terms_zero A P w v hw z (x w) (x v)
  · intro hv
    exact (hv (Finset.mem_univ v)).elim

theorem position_pairing_sum (ξ : BallGeometryData.FrameIndex A → ℂ) (x : BallGeometryData.RealPositions A) :
    (∑ v, ∑ i, ((LocalPositionInclusion.realPositionColumn A v).mulVec (x v) i : ℂ) * ξ i) =
      ∑ i, (MinkowskiCoordinatesPosition.realPositionCoordinates A x i : ℂ) * ξ i := by
  rw [realPosition_sum_columns]
  simp only [Finset.sum_apply, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gaussianValue_product (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ) (x : BallGeometryData.RealPositions A) :
    (∏ v, DataTheta.gaussianValue (PeriodCoordinates.geometricPeriod A P z).matrix ξ ((LocalPositionInclusion.realPositionColumn A v).mulVec (x v))) =
      DataTheta.gaussianValue (PeriodCoordinates.geometricPeriod A P z).matrix ξ (MinkowskiCoordinatesPosition.realPositionCoordinates A x) := by
  simp only [DataTheta.gaussianValue]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← period_quadratic_sum A P z x, position_pairing_sum]

theorem archGaussian_product (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ) (x : BallGeometryData.RealPositions A) :
    DataTheta.archTestValue (A := A) (GeometricGaussians.gaussianFamily A P z ξ) x =
      DataTheta.gaussianValue (PeriodCoordinates.geometricPeriod A P z).matrix ξ (MinkowskiCoordinatesPosition.realPositionCoordinates A x) := by
  simp only [DataTheta.archTestValue, GeometricGaussians.gaussianFamily_enumerate, LocalGaussianValues.nativeGaussian_real_value]
  simp only [← LocalPositionInclusion.realPositionColumn_apply]
  exact gaussianValue_product A P z ξ x

end RepresentationTheory.Theta.Adelic.GaussianProduct

namespace RepresentationTheory.Theta.Adelic.GaussianProduct.ThetaComparison

/-! The literal rational Gaussian sum agrees with the independently
constructed adelic theta functional for the actual native test family. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.GaussianProduct
open OAI.RepresentationTheory.Theta.Adelic.Evaluation

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem archimedeanValue_real_coordinates (φ : ThetaEvaluation.ArchimedeanTests F (3 * m)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    ThetaEvaluation.archimedeanValue F (3 * m) φ x = DataTheta.archTestValue (A := A) φ (BallGeometryData.archPositions A x) := by
  simp only [ThetaEvaluation.archimedeanValue, DataTheta.archTestValue, BallGeometryData.archPositions, RingEquiv.symm_apply_apply]
  exact (Equiv.prod_comp A.enumerate (fun v => (φ v).val
    (fun i => Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl v) (x i)))).symm

theorem archGaussian_rational_value (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    ThetaEvaluation.archimedeanValue F (3 * m) (GeometricGaussians.gaussianFamily A P z ξ) x =
      DataTheta.gaussianValue (PeriodCoordinates.geometricPeriod A P z).matrix ξ (fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ)) := by
  rw [archimedeanValue_real_coordinates A, archGaussian_product]
  exact congrArg (DataTheta.gaussianValue (PeriodCoordinates.geometricPeriod A P z).matrix ξ)
    (funext (MinkowskiCoordinatesPosition.realPositionCoordinates_rational A x))

theorem thetaSummand_native (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (z : BallNatural.Ball)
    (ξ : BallGeometryData.FrameIndex A → ℂ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    DataTheta.thetaSummand (GeometricGaussians.constructedComparison A P) f (PeriodCoordinates.geometricPeriod A P z).matrix ξ x =
      ThetaEvaluation.summand F (3 * m) (GeometricGaussians.gaussianFamily A P z ξ) f x := by
  change DataTheta.rationalWeight f x * DataTheta.gaussianValue (PeriodCoordinates.geometricPeriod A P z).matrix ξ
    (fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ)) =
      ThetaEvaluation.archimedeanValue F (3 * m) (GeometricGaussians.gaussianFamily A P z ξ) x * DataTheta.rationalWeight f x
  rw [archGaussian_rational_value]
  exact mul_comm _ _

theorem ball_theta_summable (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ) :
    Summable (DataTheta.thetaSummand (GeometricGaussians.constructedComparison A P) f (PeriodCoordinates.geometricPeriod A P z).matrix ξ) :=
  (ThetaEvaluation.summand_summable F (3 * m) (GeometricGaussians.gaussianFamily A P z ξ) f).congr
    (fun x => (thetaSummand_native A P f z ξ x).symm)

theorem rationalTheta_native (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (z : BallNatural.Ball) (ξ : BallGeometryData.FrameIndex A → ℂ) :
    DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) f (PeriodCoordinates.geometricPeriod A P z).matrix ξ =
      ThetaEvaluation.theta F (3 * m) (GeometricGaussians.gaussianFamily A P z ξ) f := by
  apply tsum_congr
  intro x
  exact thetaSummand_native A P f z ξ x

end RepresentationTheory.Theta.Adelic.GaussianProduct.ThetaComparison

end

end OAI
